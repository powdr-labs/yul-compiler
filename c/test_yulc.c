/*
 * test_yulc.c - exercises the yulc C interface.
 *
 * With a file argument it mirrors the yulc CLI: print the compiled bytecode
 * as lowercase hex on stdout and exit 0, or report the failure on stderr and
 * exit with the yulc status code. scripts/build-c-lib.sh diffs this against
 * `lake exe yulc` on the same input.
 *
 * Without arguments it runs a built-in self-test: a block-rooted program, an
 * object-rooted program (the shape solc's --ir output has), a repeated
 * compile on the already-initialized runtime, a parse error, and NULL/invalid
 * argument handling.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "include/yulc.h"

static int compile_file(const char *path) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    fprintf(stderr, "%s: cannot open\n", path);
    return 66;
  }
  fseek(f, 0, SEEK_END);
  long size = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *source = malloc((size_t)size + 1);
  if (source == NULL || fread(source, 1, (size_t)size, f) != (size_t)size) {
    fprintf(stderr, "%s: cannot read\n", path);
    fclose(f);
    free(source);
    return 66;
  }
  fclose(f);
  source[size] = '\0';

  uint8_t *bytecode = NULL;
  size_t len = 0;
  int status = yulc_compile(source, &bytecode, &len);
  free(source);
  if (status != YULC_OK) {
    fprintf(stderr, "%s: %s\n", path, yulc_status_string(status));
    return status;
  }
  for (size_t i = 0; i < len; i++)
    printf("%02x", bytecode[i]);
  printf("\n");
  yulc_free(bytecode);
  return 0;
}

static int failures = 0;

static void expect(int cond, const char *what) {
  if (!cond) {
    fprintf(stderr, "FAIL: %s\n", what);
    failures++;
  } else {
    fprintf(stderr, "ok: %s\n", what);
  }
}

static void expect_status(const char *source, int expected, const char *what) {
  uint8_t *bytecode = NULL;
  size_t len = 0;
  int status = yulc_compile(source, &bytecode, &len);
  expect(status == expected, what);
  if (status == YULC_OK) {
    expect(bytecode != NULL, "successful compile returns a buffer");
    expect(len > 0, "bytecode is nonempty");
  } else {
    expect(bytecode == NULL && len == 0,
           "failed compile leaves the out-parameters empty");
  }
  yulc_free(bytecode);
}

static int self_test(void) {
  expect(yulc_init() == YULC_OK, "yulc_init");
  expect(yulc_init() == YULC_OK, "yulc_init is idempotent");

  expect_status("{ mstore(0, 42) return(0, 32) }", YULC_OK,
                "block-rooted program compiles");

  expect_status("object \"Contract\" {\n"
                "  code {\n"
                "    datacopy(0, dataoffset(\"runtime\"), datasize(\"runtime\"))\n"
                "    return(0, datasize(\"runtime\"))\n"
                "  }\n"
                "  object \"runtime\" {\n"
                "    code { mstore(0, 7) return(0, 32) }\n"
                "  }\n"
                "}",
                YULC_OK, "object-rooted program compiles");

  expect_status("{ mstore(0, 1) }", YULC_OK,
                "second compile on a warm runtime");

  expect_status("{ let x := }", YULC_ERROR_PARSE, "parse error is reported");

  uint8_t *bytecode = (uint8_t *)&failures;
  size_t len = 99;
  expect(yulc_compile(NULL, &bytecode, &len) == YULC_ERROR_INTERNAL &&
             bytecode == NULL && len == 0,
         "NULL source is rejected");
  expect(yulc_compile("{ }", NULL, &len) == YULC_ERROR_INTERNAL,
         "NULL out-parameter is rejected");
  expect(yulc_compile("{ \xff }", &bytecode, &len) == YULC_ERROR_INTERNAL,
         "invalid UTF-8 is rejected");

  yulc_free(NULL); /* must be a no-op */

  if (failures) {
    fprintf(stderr, "%d self-test failure(s)\n", failures);
    return 1;
  }
  fprintf(stderr, "all self-tests passed\n");
  return 0;
}

int main(int argc, char **argv) {
  if (argc == 2)
    return compile_file(argv[1]);
  if (argc == 1)
    return self_test();
  fprintf(stderr, "usage: %s [file.yul]\n", argv[0]);
  return 64;
}
