# Upstream Yul tests

`solidity-yul-syntax-known-mismatches.txt` records the expected differences
between this parser and Solidity's complete Yul syntax corpus.

`solidity-yul-interpreter-tests.txt` selects executable fixtures from
Solidity's `test/libyul/yulInterpreterTests` directory. CI compiles each
selected Yul program to EVM bytecode, runs it with `evm-semantics` in the
fixed environment used by Solidity's Yul interpreter tests, and compares the
complete nonzero memory, storage, and transient-storage post-state with the
dumps embedded in the `.yul` file.

The initial state has empty calldata, memory, storage, and transient storage.
It also reproduces Solidity's fixed address, caller, call value, balances,
block number, timestamp, fees, chain ID, and other block fields. The executing
account's code is the bytecode produced by this compiler, rather than the dummy
`codecodecodecodecode` value used by Solidity's AST interpreter.

Add a relative fixture path to the manifest when its language features are
supported. A local checkout can be checked with:

```sh
lake env lean --run scripts/CheckSolidityInterpreterTests.lean \
  /path/to/solidity/test/libyul/yulInterpreterTests \
  test/solidity-yul-interpreter-tests.txt
```
