// Uniswap v4-core LiquidityMath gas benchmark, mirroring test/libraries/LiquidityMath.t.sol.
// Library bodies are verbatim v4-core src/libraries sources, flattened
// (SPDX/pragma/import lines dropped).
//
// The wrapper contract's name must sort alphabetically before every library in
// this file: solc emits one output section per contract, ordered by name, and
// the gas harness reads the first one.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

contract AGasTest {
    function addDelta(uint128 x, int128 y) external pure returns (uint128) {
        return LiquidityMath.addDelta(x, y);
    }
}

/// @title Math library for liquidity
library LiquidityMath {
    /// @notice Add a signed liquidity delta to liquidity and revert if it overflows or underflows
    /// @param x The liquidity before change
    /// @param y The delta by which liquidity should be changed
    /// @return z The liquidity delta
    function addDelta(uint128 x, int128 y) internal pure returns (uint128 z) {
        assembly ("memory-safe") {
            z := add(and(x, 0xffffffffffffffffffffffffffffffff), signextend(15, y))
            if shr(128, z) {
                // revert SafeCastOverflow()
                mstore(0, 0x93dafdf1)
                revert(0x1c, 0x04)
            }
        }
    }
}

// ----
// addDelta(uint128,int128): 100, -50 -> 50
// addDelta(uint128,int128): 1000000000000000000, 100000000000000000 -> 1100000000000000000
// addDelta(uint128,int128): 0, 0 -> 0
