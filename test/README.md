# Upstream Yul tests

`solidity-yul-syntax-known-mismatches.txt` records expected differences between
this parser/validator and Solidity's complete Yul syntax corpus. It is currently
empty: every upstream success is accepted and every fixture containing an
`*Error` expectation is rejected.

`solidity-yul-interpreter-known-failures.txt` records the fixtures that do not
yet work from Solidity's complete `test/libyul/yulInterpreterTests` corpus.
CI attempts to compile and execute every Yul program with `evm-semantics` in
the fixed environment used by Solidity's Yul interpreter tests, then compares
the complete nonzero memory, storage, and transient-storage post-state with
the dumps embedded in the `.yul` file. A new failure or a stale baseline entry
makes CI fail.

The initial state has empty calldata, memory, storage, and transient storage.
It also reproduces Solidity's fixed address, caller, call value, balances,
block number, timestamp, fees, chain ID, and other block fields. The executing
account's code is the bytecode produced by this compiler, rather than the dummy
`codecodecodecodecode` value used by Solidity's AST interpreter.

Remove a relative fixture path from either baseline as soon as it passes. A
local checkout can be checked with:

```sh
lake env lean --run scripts/CheckSoliditySyntaxTests.lean \
  /path/to/solidity/test/libyul/yulSyntaxTests \
  test/solidity-yul-syntax-known-mismatches.txt
```

Interpreter fixtures can be checked with:

```sh
lake env lean --run scripts/CheckSolidityInterpreterTests.lean \
  /path/to/solidity/test/libyul/yulInterpreterTests \
  test/solidity-yul-interpreter-known-failures.txt
```
