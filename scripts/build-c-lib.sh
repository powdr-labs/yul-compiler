#!/usr/bin/env bash
#
# build-c-lib.sh — build the C-callable compiler libraries (see c/).
#
# Produces, under .lake/build/c/:
#   libyulc.so   shared library with the whole Lean-compiled compiler linked
#                in statically. The Lean runtime itself must stay dynamic
#                (libleanrt.a is built with local-exec TLS, which no linker
#                accepts inside a DSO), so libyulc.so depends on
#                libleanshared.so and libLake_shared.so; both are copied next
#                to it and found through an $ORIGIN rpath. Linking a plain
#                gcc/clang build (such as solc's) needs just
#                `-L <this dir> -lyulc`, and shipping means shipping the
#                directory.
#   libyulc.a    the full closure, Lean runtime included, merged into one
#                static archive. Usable from any C or C++ toolchain with
#                `-lyulc -lpthread -ldl -lrt -lm` when linking an
#                *executable* (the local-exec TLS above means it cannot be
#                folded into somebody else's shared library; the Lean
#                runtime's libc++ is inside, namespaced under std::__1, so
#                it coexists with libstdc++).
#   yulc.h       the public header, copied from c/include/.
#
# The exported interface is defined in c/include/yulc.h and implemented by
# c/yulc.c on top of the @[export] wrappers in YulCApi.lean.
#
# With --test, additionally builds c/test_yulc.c against BOTH libraries, runs
# the self-tests, and differentially checks the hex output against
# `lake exe yulc` on a handful of embedded programs. An optional directory
# after --test adds every *.yul file under it to that differential (e.g. a
# dump of solc --ir output).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

CC="${CC:-cc}"
LEAN_PREFIX="$(lean --print-prefix)"
OUT=.lake/build/c
mkdir -p "$OUT"

echo "== building static facets of the compiler libraries" >&2
# The `yulc` executable is built first because an executable link is the only
# target whose dependencies are the *whole* transitive import closure: a
# library's `:static` facet only compiles the modules the library's own root
# reaches, so a module that just one importer outside that root pulls in
# (YulParser.Compile imports YulEvmCompiler.Optimizer.Implementation.
# MemorySpillSelect, which YulEvmCompiler.lean does not) never gets an object
# file, and the archives below silently come out incomplete. Requesting the
# executable makes every object the merged library needs exist by
# construction; `lake build yulc` later (for the --test differential) is then
# a no-op.
#
# YulCApi holds the @[export] entry points and is not reachable from the
# executable, so it and its Lake dependencies are still requested explicitly.
lake build yulc \
  YulCApi:static YulParser:static YulEvmCompiler:static \
  yul-semantics/YulSemantics:static evm_semantics/EvmSemantics:static \
  mathlib/Mathlib:static batteries/Batteries:static \
  batteries/BatteriesRecycling:static aesop/Aesop:static \
  Qq/Qq:static proofwidgets/ProofWidgets:static \
  importGraph/ImportGraph:static LeanSearchClient/LeanSearchClient:static \
  plausible/Plausible:static Cli/Cli:static

# One archive per package, regenerated from every compiled module object under
# the package's build/ir tree. The per-library archives Lake produces are NOT
# used directly because a library's glob can miss modules that other packages
# import as loose module targets (e.g. Mathlib imports
# ProofWidgets.Component.RefreshComponent, which the ProofWidgets root never
# imports, so it is compiled but not archived); collecting the objects
# directly makes the closure complete by construction. Unreferenced members
# are simply never pulled in by the linker.
echo "== collecting per-package archives" >&2
PACKAGE_DIRS=(
  .
  .lake/packages/yul-semantics
  .lake/packages/evm_semantics
  .lake/packages/mathlib
  .lake/packages/batteries
  .lake/packages/aesop
  .lake/packages/Qq
  .lake/packages/proofwidgets
  .lake/packages/importGraph
  .lake/packages/LeanSearchClient
  .lake/packages/plausible
  .lake/packages/Cli
)
ARCHIVES=()
mkdir -p "$OUT/pkg"
for dir in "${PACKAGE_DIRS[@]}"; do
  if [[ "$dir" == "." ]]; then name=yul-evm-compiler; else name="$(basename "$dir")"; fi
  archive="$OUT/pkg/lib_pkg_$name.a"
  rm -f "$archive"
  # Skip stale objects whose .lean source is gone: Lake never garbage-collects
  # build/ir, so a renamed or deleted module would otherwise leave a duplicate
  # definition of every symbol it exported.
  find "$dir/.lake/build/ir" -name '*.c.o.export' -print0 | sort -z |
    while IFS= read -r -d '' obj; do
      rel="${obj#"$dir/.lake/build/ir/"}"
      [[ -f "$dir/${rel%.c.o.export}.lean" ]] && printf '%s\0' "$obj"
    done | xargs -0 ar q "$archive"
  ranlib "$archive"
  ARCHIVES+=("$archive")
done

# Static Lean runtime pieces for the merged archive, mirroring
# `leanc --print-ldflags`. libLake.a is included because ImportGraph (reached
# through Mathlib) references Lake symbols.
LEAN_RUNTIME=(
  "$LEAN_PREFIX/lib/lean/libLake.a"
  "$LEAN_PREFIX/lib/lean/libleancpp.a"
  "$LEAN_PREFIX/lib/lean/libLean.a"
  "$LEAN_PREFIX/lib/lean/libStd.a"
  "$LEAN_PREFIX/lib/lean/libInit.a"
  "$LEAN_PREFIX/lib/lean/libleanrt.a"
  "$LEAN_PREFIX/lib/libc++.a"
  "$LEAN_PREFIX/lib/libc++abi.a"
  "$LEAN_PREFIX/lib/libgmp.a"
  "$LEAN_PREFIX/lib/libuv.a"
)

echo "== compiling the C shim" >&2
# The shim is compiled with the system compiler on purpose: it proves the
# public header needs nothing from the Lean toolchain besides <lean/lean.h>.
"$CC" -O2 -fPIC -Wall -Wextra -I "$LEAN_PREFIX/include" \
  -c -o "$OUT/yulc.o" c/yulc.c

echo "== linking $OUT/libyulc.so" >&2
# The system compiler drives this link: the compiler archives are plain PIC
# objects, and the Lean runtime comes from libleanshared.so/libLake_shared.so
# (Lake because ImportGraph, reached through Mathlib, references it). The
# $ORIGIN rpath makes the copied runtime libraries load-time-visible wherever
# the output directory is shipped.
"$CC" -shared -o "$OUT/libyulc.so" "$OUT/yulc.o" \
  -Wl,--start-group "${ARCHIVES[@]}" -Wl,--end-group \
  "$LEAN_PREFIX/lib/lean/libleanshared.so" \
  "$LEAN_PREFIX/lib/lean/libLake_shared.so" \
  -Wl,-rpath,'$ORIGIN' -Wl,--no-undefined \
  -lpthread -ldl -lrt -lm
cp -f "$LEAN_PREFIX/lib/lean/libleanshared.so" \
  "$LEAN_PREFIX/lib/lean/libLake_shared.so" "$OUT/"
chmod +x "$OUT/libleanshared.so" "$OUT/libLake_shared.so"

# A self-contained library must not leave Lean symbols dangling; ld.bfd only
# reports them when an executable later links against the library, which is
# too late. Fail here instead.
if ! "$CC" -O2 -x c - -o /dev/null -L "$OUT" -lyulc \
    -Wl,-rpath,"$PWD/$OUT" <<'EOF'
#include <stddef.h>
#include <stdint.h>
extern int yulc_init(void);
int main(void) { return yulc_init() == 0 ? 0 : 1; }
EOF
then
  echo "libyulc.so has unresolved symbols" >&2
  exit 1
fi

echo "== archiving $OUT/libyulc.a" >&2
{
  echo "create $OUT/libyulc.a"
  echo "addmod $OUT/yulc.o"
  for a in "${ARCHIVES[@]}" "${LEAN_RUNTIME[@]}"; do
    echo "addlib $a"
  done
  echo "save"
  echo "end"
} | ar -M
ranlib "$OUT/libyulc.a"

cp c/include/yulc.h "$OUT/yulc.h"
ls -lh "$OUT/libyulc.so" "$OUT/libyulc.a" >&2

if [[ "${1:-}" != "--test" ]]; then
  exit 0
fi

echo "== building test clients (system compiler, no Lean toolchain flags)" >&2
"$CC" -O2 -Wall -Wextra -I c -o "$OUT/test_yulc_shared" c/test_yulc.c \
  -L "$OUT" -lyulc -Wl,-rpath,"$PWD/$OUT"
"$CC" -O2 -Wall -Wextra -I c -o "$OUT/test_yulc_static" c/test_yulc.c \
  "$OUT/libyulc.a" -lpthread -ldl -lrt -lm

echo "== self-tests (shared)" >&2
"$OUT/test_yulc_shared"
echo "== self-tests (static)" >&2
"$OUT/test_yulc_static"

echo "== differential against lake exe yulc" >&2
lake build yulc >&2
YULC_BIN=.lake/build/bin/yulc

SAMPLES="$OUT/samples"
mkdir -p "$SAMPLES"
cat > "$SAMPLES/block.yul" <<'EOF'
{
    let x := 2
    let y := 40
    sstore(0, add(x, y))
    mstore(0, mload(0))
    return(0, 32)
}
EOF
cat > "$SAMPLES/object.yul" <<'EOF'
object "Contract" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            switch shr(224, calldataload(0))
            case 0x371303c0 { sstore(0, add(sload(0), 1)) }
            default { revert(0, 0) }
        }
    }
}
EOF
cat > "$SAMPLES/functions.yul" <<'EOF'
{
    function fib(n) -> r {
        r := 1
        let prev := 0
        for { let i := 0 } lt(i, n) { i := add(i, 1) } {
            let next := add(r, prev)
            prev := r
            r := next
        }
    }
    sstore(0, fib(10))
}
EOF
cat > "$SAMPLES/parse-error.yul" <<'EOF'
{ let x := }
EOF

checked=0
while IFS= read -r fixture; do
  expected_status=0
  expected="$("$YULC_BIN" "$fixture" 2>/dev/null)" || expected_status=$?
  actual_status=0
  actual="$("$OUT/test_yulc_shared" "$fixture" 2>/dev/null)" || actual_status=$?
  if [[ "$expected_status" != "$actual_status" || "$expected" != "$actual" ]]; then
    echo "MISMATCH on $fixture: yulc exit $expected_status vs C API exit $actual_status" >&2
    exit 1
  fi
  checked=$((checked + 1))
done < <({ find "$SAMPLES" -name '*.yul'; \
           [[ -n "${2:-}" ]] && find "$2" -name '*.yul'; } | sort)
echo "== $checked fixtures agree with the yulc CLI" >&2
