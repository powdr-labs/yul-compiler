// Uniswap v4-core UnsafeMath gas benchmark, mirroring test/libraries/UnsafeMath.t.sol.
// Library bodies are verbatim v4-core src/libraries sources, flattened
// (SPDX/pragma/import lines dropped).
//
// The wrapper contract's name must sort alphabetically before every library in
// this file: solc emits one output section per contract, ordered by name, and
// the gas harness reads the first one.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

contract AGasTest {
    function divRoundingUp(uint256 x, uint256 y) external pure returns (uint256) {
        return UnsafeMath.divRoundingUp(x, y);
    }

    function simpleMulDiv(uint256 a, uint256 b, uint256 denominator) external pure returns (uint256) {
        return UnsafeMath.simpleMulDiv(a, b, denominator);
    }
}

/// @title Math functions that do not check inputs or outputs
/// @notice Contains methods that perform common math functions but do not do any overflow or underflow checks
library UnsafeMath {
    /// @notice Returns ceil(x / y)
    /// @dev division by 0 will return 0, and should be checked externally
    /// @param x The dividend
    /// @param y The divisor
    /// @return z The quotient, ceil(x / y)
    function divRoundingUp(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly ("memory-safe") {
            z := add(div(x, y), gt(mod(x, y), 0))
        }
    }

    /// @notice Calculates floor(a×b÷denominator)
    /// @dev division by 0 will return 0, and should be checked externally
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return result The 256-bit result, floor(a×b÷denominator)
    function simpleMulDiv(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256 result) {
        assembly ("memory-safe") {
            result := div(mul(a, b), denominator)
        }
    }
}

// ----
// divRoundingUp(uint256,uint256): 7, 3 -> 3
// divRoundingUp(uint256,uint256): 1000000000000000000, 3 -> 333333333333333334
// simpleMulDiv(uint256,uint256,uint256): 5, 10, 2 -> 25
// simpleMulDiv(uint256,uint256,uint256): 1000000000000000000, 3, 7 -> 428571428571428571
