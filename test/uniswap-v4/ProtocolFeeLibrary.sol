// Uniswap v4-core ProtocolFeeLibrary gas benchmark, mirroring test/libraries/ProtocolFeeLibrary.t.sol.
// Library bodies are verbatim v4-core src/libraries sources, flattened
// (SPDX/pragma/import lines dropped).
//
// The wrapper contract's name must sort alphabetically before every library in
// this file: solc emits one output section per contract, ordered by name, and
// the gas harness reads the first one.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

contract AGasTest {
    function getZeroForOneFee(uint24 self) external pure returns (uint16) {
        return ProtocolFeeLibrary.getZeroForOneFee(self);
    }

    function getOneForZeroFee(uint24 self) external pure returns (uint16) {
        return ProtocolFeeLibrary.getOneForZeroFee(self);
    }

    function isValidProtocolFee(uint24 self) external pure returns (bool) {
        return ProtocolFeeLibrary.isValidProtocolFee(self);
    }

    function calculateSwapFee(uint16 self, uint24 lpFee) external pure returns (uint24) {
        return ProtocolFeeLibrary.calculateSwapFee(self, lpFee);
    }
}

/// @notice library of functions related to protocol fees
library ProtocolFeeLibrary {
    /// @notice Max protocol fee is 0.1% (1000 pips)
    /// @dev Increasing these values could lead to overflow in Pool.swap
    uint16 public constant MAX_PROTOCOL_FEE = 1000;

    /// @notice Thresholds used for optimized bounds checks on protocol fees
    uint24 internal constant FEE_0_THRESHOLD = 1001;
    uint24 internal constant FEE_1_THRESHOLD = 1001 << 12;

    /// @notice the protocol fee is represented in hundredths of a bip
    uint256 internal constant PIPS_DENOMINATOR = 1_000_000;

    function getZeroForOneFee(uint24 self) internal pure returns (uint16) {
        return uint16(self & 0xfff);
    }

    function getOneForZeroFee(uint24 self) internal pure returns (uint16) {
        return uint16(self >> 12);
    }

    function isValidProtocolFee(uint24 self) internal pure returns (bool valid) {
        // Equivalent to: getZeroForOneFee(self) <= MAX_PROTOCOL_FEE && getOneForZeroFee(self) <= MAX_PROTOCOL_FEE
        assembly ("memory-safe") {
            let isZeroForOneFeeOk := lt(and(self, 0xfff), FEE_0_THRESHOLD)
            let isOneForZeroFeeOk := lt(and(self, 0xfff000), FEE_1_THRESHOLD)
            valid := and(isZeroForOneFeeOk, isOneForZeroFeeOk)
        }
    }

    // The protocol fee is taken from the input amount first and then the LP fee is taken from the remaining
    // The swap fee is capped at 100%
    // Equivalent to protocolFee + lpFee(1_000_000 - protocolFee) / 1_000_000 (rounded up)
    /// @dev here `self` is just a single direction's protocol fee, not a packed type of 2 protocol fees
    function calculateSwapFee(uint16 self, uint24 lpFee) internal pure returns (uint24 swapFee) {
        // protocolFee + lpFee - (protocolFee * lpFee / 1_000_000)
        assembly ("memory-safe") {
            self := and(self, 0xfff)
            lpFee := and(lpFee, 0xffffff)
            let numerator := mul(self, lpFee)
            swapFee := sub(add(self, lpFee), div(numerator, PIPS_DENOMINATOR))
        }
    }
}

// ----
// getZeroForOneFee(uint24): 1000 -> 1000
// getOneForZeroFee(uint24): 4096000 -> 1000
// isValidProtocolFee(uint24): 1000 -> true
// calculateSwapFee(uint16,uint24): 1000, 3000 -> 3997
