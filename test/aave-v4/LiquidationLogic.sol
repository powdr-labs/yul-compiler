// SPDX-License-Identifier: LicenseRef-BUSL
pragma solidity ^0.8.28;

// Aave v4 compiler/gas fixture for test environments only.
// Wrapper scenarios reproduce upstream tests; production sources are flattened
// from commit cfdf931c8c61715bef590c087c1fabe64c92ac92. See LICENSE.

// src/dependencies/openzeppelin/IAccessManaged.sol

// OpenZeppelin Contracts (last updated v5.4.0) (access/manager/IAccessManaged.sol)

interface IAccessManaged {
  /**
   * @dev Authority that manages this contract was updated.
   */
  event AuthorityUpdated(address authority);

  error AccessManagedUnauthorized(address caller);
  error AccessManagedRequiredDelay(address caller, uint32 delay);
  error AccessManagedInvalidAuthority(address authority);

  /**
   * @dev Returns the current authority.
   */
  function authority() external view returns (address);

  /**
   * @dev Transfers control to a new authority. The caller must be the current authority.
   */
  function setAuthority(address) external;

  /**
   * @dev Returns true only in the context of a delayed restricted call, at the moment that the scheduled operation is
   * being consumed. Prevents denial of service for delayed restricted calls in the case that the contract performs
   * attacker controlled calls.
   */
  function isConsumingScheduledOp() external view returns (bytes4);
}

// src/dependencies/openzeppelin/IERC165.sol

// OpenZeppelin Contracts (last updated v5.4.0) (utils/introspection/IERC165.sol)

/**
 * @dev Interface of the ERC-165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[ERC].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
  /**
   * @dev Returns true if this contract implements the interface defined by
   * `interfaceId`. See the corresponding
   * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[ERC section]
   * to learn more about how these ids are created.
   *
   * This function call must use less than 30 000 gas.
   */
  function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

// src/dependencies/openzeppelin/IERC20.sol

// OpenZeppelin Contracts (last updated v5.4.0) (token/ERC20/IERC20.sol)

/**
 * @dev Interface of the ERC-20 standard as defined in the ERC.
 */
interface IERC20 {
  /**
   * @dev Emitted when `value` tokens are moved from one account (`from`) to
   * another (`to`).
   *
   * Note that `value` may be zero.
   */
  event Transfer(address indexed from, address indexed to, uint256 value);

  /**
   * @dev Emitted when the allowance of a `spender` for an `owner` is set by
   * a call to {approve}. `value` is the new allowance.
   */
  event Approval(address indexed owner, address indexed spender, uint256 value);

  /**
   * @dev Returns the value of tokens in existence.
   */
  function totalSupply() external view returns (uint256);

  /**
   * @dev Returns the value of tokens owned by `account`.
   */
  function balanceOf(address account) external view returns (uint256);

  /**
   * @dev Moves a `value` amount of tokens from the caller's account to `to`.
   *
   * Returns a boolean value indicating whether the operation succeeded.
   *
   * Emits a {Transfer} event.
   */
  function transfer(address to, uint256 value) external returns (bool);

  /**
   * @dev Returns the remaining number of tokens that `spender` will be
   * allowed to spend on behalf of `owner` through {transferFrom}. This is
   * zero by default.
   *
   * This value changes when {approve} or {transferFrom} are called.
   */
  function allowance(address owner, address spender) external view returns (uint256);

  /**
   * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
   * caller's tokens.
   *
   * Returns a boolean value indicating whether the operation succeeded.
   *
   * IMPORTANT: Beware that changing an allowance with this method brings the risk
   * that someone may use both the old and the new allowance by unfortunate
   * transaction ordering. One possible solution to mitigate this race
   * condition is to first reduce the spender's allowance to 0 and set the
   * desired value afterwards:
   * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
   *
   * Emits an {Approval} event.
   */
  function approve(address spender, uint256 value) external returns (bool);

  /**
   * @dev Moves a `value` amount of tokens from `from` to `to` using the
   * allowance mechanism. `value` is then deducted from the caller's
   * allowance.
   *
   * Returns a boolean value indicating whether the operation succeeded.
   *
   * Emits a {Transfer} event.
   */
  function transferFrom(address from, address to, uint256 value) external returns (bool);
}

// src/interfaces/IExtSload.sol

/// @title IExtSload
/// @author Aave Labs
/// @notice Minimal interface to easily access storage of source contract externally. See https://eips.ethereum.org/EIPS/eip-2330#rationale.
interface IExtSload {
  /// @notice Returns the storage `value` of this contract at a given `slot`.
  /// @param slot Slot to SLOAD from.
  function extSload(bytes32 slot) external view returns (bytes32 value);

  /// @notice Returns the storage `values` of this contract at the given `slots`.
  /// @param slots Array of slots to SLOAD from.
  function extSloads(bytes32[] calldata slots) external view returns (bytes32[] memory values);
}

// src/hub/interfaces/IHubBase.sol

/// @title IHubBase
/// @author Aave Labs
/// @notice Minimal interface for Hub.
interface IHubBase {
  /// @notice Changes to premium owed accounting.
  /// @dev sharesDelta The change in premium shares.
  /// @dev offsetRayDelta The change in premium offset, expressed in asset units and scaled by RAY.
  /// @dev restoredPremiumRay The restored premium, expressed in asset units and scaled by RAY.
  struct PremiumDelta {
    int256 sharesDelta;
    int256 offsetRayDelta;
    uint256 restoredPremiumRay;
  }

  /// @notice Emitted on the `add` action.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @param shares The amount of shares added.
  /// @param amount The amount of assets added.
  event Add(uint256 indexed assetId, address indexed spoke, uint256 shares, uint256 amount);

  /// @notice Emitted on the `remove` action.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @param shares The amount of shares removed.
  /// @param amount The amount of assets removed.
  event Remove(uint256 indexed assetId, address indexed spoke, uint256 shares, uint256 amount);

  /// @notice Emitted on the `draw` action.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @param drawnShares The amount of drawn shares.
  /// @param drawnAmount The amount of drawn assets.
  event Draw(
    uint256 indexed assetId,
    address indexed spoke,
    uint256 drawnShares,
    uint256 drawnAmount
  );

  /// @notice Emitted on the `restore` action.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @param drawnShares The amount of drawn shares.
  /// @param premiumDelta The premium delta data struct.
  /// @param drawnAmount The amount of drawn assets restored.
  /// @param premiumAmount The amount of premium assets restored.
  event Restore(
    uint256 indexed assetId,
    address indexed spoke,
    uint256 drawnShares,
    PremiumDelta premiumDelta,
    uint256 drawnAmount,
    uint256 premiumAmount
  );

  /// @notice Emitted on the `refreshPremium` action.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @param premiumDelta The premium delta data struct.
  event RefreshPremium(uint256 indexed assetId, address indexed spoke, PremiumDelta premiumDelta);

  /// @notice Emitted on the `reportDeficit` action.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @param drawnShares The amount of drawn shares reported as deficit.
  /// @param premiumDelta The premium delta data struct.
  /// @param deficitAmountRay The amount of deficit reported, expressed in asset units and scaled by RAY.
  event ReportDeficit(
    uint256 indexed assetId,
    address indexed spoke,
    uint256 drawnShares,
    PremiumDelta premiumDelta,
    uint256 deficitAmountRay
  );

  /// @notice Emitted on the `transferShares` action.
  /// @param assetId The identifier of the asset.
  /// @param sender The address of the sender.
  /// @param receiver The address of the receiver.
  /// @param shares The amount of shares transferred.
  event TransferShares(
    uint256 indexed assetId,
    address indexed sender,
    address indexed receiver,
    uint256 shares
  );

  /// @notice Adds assets on behalf of a user.
  /// @dev Only callable by active spokes.
  /// @dev Underlying assets must be transferred to the Hub before invocation.
  /// @dev Extra untracked underlying liquidity in the Hub can be skimmed into the Hub's liquidity accounting through this action.
  /// @param assetId The identifier of the asset.
  /// @param amount The amount of asset liquidity to add.
  /// @return The amount of shares added.
  function add(uint256 assetId, uint256 amount) external returns (uint256);

  /// @notice Removes assets on behalf of a user.
  /// @dev Only callable by active spokes.
  /// @param assetId The identifier of the asset.
  /// @param amount The amount of asset liquidity to remove.
  /// @param to The address to transfer the assets to.
  /// @return The amount of shares removed.
  function remove(uint256 assetId, uint256 amount, address to) external returns (uint256);

  /// @notice Draws assets on behalf of a user.
  /// @dev Only callable by active spokes.
  /// @param assetId The identifier of the asset.
  /// @param amount The amount of assets to draw.
  /// @param to The address to transfer the underlying assets to.
  /// @return The amount of drawn shares.
  function draw(uint256 assetId, uint256 amount, address to) external returns (uint256);

  /// @notice Restores assets on behalf of a user.
  /// @dev Only callable by active spokes.
  /// @dev Interest is always paid off first from premium, then from drawn.
  /// @dev Underlying assets must be transferred to the Hub before invocation.
  /// @dev Extra untracked underlying liquidity in the Hub can be skimmed into the Hub's liquidity accounting through this action.
  /// @param assetId The identifier of the asset.
  /// @param drawnAmount The drawn amount to restore.
  /// @param premiumDelta The premium delta to apply which signals premium repayment.
  /// @return The amount of drawn shares restored.
  function restore(
    uint256 assetId,
    uint256 drawnAmount,
    PremiumDelta calldata premiumDelta
  ) external returns (uint256);

  /// @notice Reports an owed amount by the caller Spoke as a deficit.
  /// @dev Only callable by active spokes.
  /// @param assetId The identifier of the asset.
  /// @param drawnAmount The drawn amount to report as deficit.
  /// @param premiumDelta The premium delta to apply which signals premium deficit.
  /// @return The amount of drawn shares reported as deficit.
  /// @return The amount of deficit reported, expressed in asset units.
  function reportDeficit(
    uint256 assetId,
    uint256 drawnAmount,
    PremiumDelta calldata premiumDelta
  ) external returns (uint256, uint256);

  /// @notice Refreshes premium accounting.
  /// @dev Only callable by active spokes.
  /// @dev Asset and spoke premium should not decrease.
  /// @param assetId The identifier of the asset.
  /// @param premiumDelta The change in premium.
  function refreshPremium(uint256 assetId, PremiumDelta calldata premiumDelta) external;

  /// @notice Transfers an amount of added shares of the caller Spoke to the fee receiver Spoke.
  /// @dev It can be used to execute one-time payments to the fee receiver Spoke (e.g., liquidation fees).
  /// @dev Only callable by active spokes.
  /// @param assetId The identifier of the asset.
  /// @param shares The amount of shares to pay to feeReceiver.
  function payFeeShares(uint256 assetId, uint256 shares) external;

  /// @notice Converts the specified amount of assets to shares upon an `add` action.
  /// @dev Rounds down to the nearest shares amount.
  /// @dev Defaults to a 1:1 exchange rate.
  /// @param assetId The identifier of the asset.
  /// @param assets The amount of assets to convert to shares amount.
  /// @return The amount of shares converted from assets amount.
  function previewAddByAssets(uint256 assetId, uint256 assets) external view returns (uint256);

  /// @notice Converts the specified shares amount to assets amount added upon an `add` action.
  /// @dev Rounds up to the nearest assets amount.
  /// @dev Defaults to a 1:1 exchange rate.
  /// @param assetId The identifier of the asset.
  /// @param shares The amount of shares to convert to assets amount.
  /// @return The amount of assets converted from shares amount.
  function previewAddByShares(uint256 assetId, uint256 shares) external view returns (uint256);

  /// @notice Converts the specified amount of assets to shares amount removed upon a `remove` action.
  /// @dev Rounds up to the nearest shares amount.
  /// @dev Defaults to a 1:1 exchange rate.
  /// @param assetId The identifier of the asset.
  /// @param assets The amount of assets to convert to shares amount.
  /// @return The amount of shares converted from assets amount.
  function previewRemoveByAssets(uint256 assetId, uint256 assets) external view returns (uint256);

  /// @notice Converts the specified amount of shares to assets amount removed upon a `remove` action.
  /// @dev Rounds down to the nearest assets amount.
  /// @dev Defaults to a 1:1 exchange rate.
  /// @param assetId The identifier of the asset.
  /// @param shares The amount of shares to convert to assets amount.
  /// @return The amount of assets converted from shares amount.
  function previewRemoveByShares(uint256 assetId, uint256 shares) external view returns (uint256);

  /// @notice Converts the specified amount of assets to shares amount drawn upon a `draw` action.
  /// @dev Rounds up to the nearest shares amount.
  /// @param assetId The identifier of the asset.
  /// @param assets The amount of assets to convert to shares amount.
  /// @return The amount of shares converted from assets amount.
  function previewDrawByAssets(uint256 assetId, uint256 assets) external view returns (uint256);

  /// @notice Converts the specified amount of shares to assets amount drawn upon a `draw` action.
  /// @dev Rounds down to the nearest assets amount.
  /// @param assetId The identifier of the asset.
  /// @param shares The amount of shares to convert to assets amount.
  /// @return The amount of assets converted from shares amount.
  function previewDrawByShares(uint256 assetId, uint256 shares) external view returns (uint256);

  /// @notice Converts the specified amount of assets to shares amount restored upon a `restore` action.
  /// @dev Rounds down to the nearest shares amount.
  /// @param assetId The identifier of the asset.
  /// @param assets The amount of assets to convert to shares amount.
  /// @return The amount of shares converted from assets amount.
  function previewRestoreByAssets(uint256 assetId, uint256 assets) external view returns (uint256);

  /// @notice Converts the specified amount of shares to assets amount restored upon a `restore` action.
  /// @dev Rounds up to the nearest assets amount.
  /// @param assetId The identifier of the asset.
  /// @param shares The amount of drawn shares to convert to assets amount.
  /// @return The amount of assets converted from shares amount.
  function previewRestoreByShares(uint256 assetId, uint256 shares) external view returns (uint256);

  /// @notice Returns the asset identifier for the specified underlying asset.
  /// @dev Reverts with `AssetNotListed` if the underlying is not listed.
  /// @param underlying The address of the underlying asset.
  function getAssetId(address underlying) external view returns (uint256);

  /// @notice Returns the underlying address and decimals of the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The underlying address of the asset.
  /// @return The decimals of the asset.
  function getAssetUnderlyingAndDecimals(uint256 assetId) external view returns (address, uint8);

  /// @notice Calculates the current drawn index for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The current drawn index of the asset.
  function getAssetDrawnIndex(uint256 assetId) external view returns (uint256);

  /// @notice Returns the total amount of the specified asset added to the Hub.
  /// @param assetId The identifier of the asset.
  /// @return The amount of the asset added.
  function getAddedAssets(uint256 assetId) external view returns (uint256);

  /// @notice Returns the total amount of shares of the specified asset added to the Hub.
  /// @param assetId The identifier of the asset.
  /// @return The amount of shares of the asset added.
  function getAddedShares(uint256 assetId) external view returns (uint256);

  /// @notice Returns the amount of owed drawn and premium assets for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The amount of owed drawn assets.
  /// @return The amount of owed premium assets.
  function getAssetOwed(uint256 assetId) external view returns (uint256, uint256);

  /// @notice Returns the total amount of assets owed to the Hub.
  /// @param assetId The identifier of the asset.
  /// @return The total amount of the assets owed.
  function getAssetTotalOwed(uint256 assetId) external view returns (uint256);

  /// @notice Returns the amount of owed premium with full precision for specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The amount of premium owed, expressed in asset units and scaled by RAY.
  function getAssetPremiumRay(uint256 assetId) external view returns (uint256);

  /// @notice Returns the amount of drawn shares of the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The amount of drawn shares.
  function getAssetDrawnShares(uint256 assetId) external view returns (uint256);

  /// @notice Returns the information regarding premium shares of the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The amount of premium shares owed to the asset.
  /// @return The premium offset of the asset, expressed in asset units and scaled by RAY.
  function getAssetPremiumData(uint256 assetId) external view returns (uint256, int256);

  /// @notice Returns the amount of available liquidity for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The amount of available liquidity.
  function getAssetLiquidity(uint256 assetId) external view returns (uint256);

  /// @notice Returns the amount of deficit with full precision of the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The amount of deficit, expressed in asset units and scaled by RAY.
  function getAssetDeficitRay(uint256 assetId) external view returns (uint256);

  /// @notice Returns the total amount of the specified assets added to the Hub by the specified spoke.
  /// @dev If spoke is `asset.feeReceiver`, includes converted `unrealizedFeeShares` in return value.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The amount of added assets.
  function getSpokeAddedAssets(uint256 assetId, address spoke) external view returns (uint256);

  /// @notice Returns the total amount of shares of the specified asset added to the Hub by the specified spoke.
  /// @dev If spoke is `asset.feeReceiver`, includes `unrealizedFeeShares` in return value.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The amount of added shares.
  function getSpokeAddedShares(uint256 assetId, address spoke) external view returns (uint256);

  /// @notice Returns the amount of the specified assets owed to the Hub by the specified spoke.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The amount of owed drawn assets.
  /// @return The amount of owed premium assets.
  function getSpokeOwed(uint256 assetId, address spoke) external view returns (uint256, uint256);

  /// @notice Returns the total amount of the specified asset owed to the Hub by the specified spoke.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The total amount of the asset owed.
  function getSpokeTotalOwed(uint256 assetId, address spoke) external view returns (uint256);

  /// @notice Returns the amount of owed premium with full precision for specified asset and spoke.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The amount of owed premium assets, expressed in asset units and scaled by RAY.
  function getSpokePremiumRay(uint256 assetId, address spoke) external view returns (uint256);

  /// @notice Returns the amount of drawn shares of the specified asset by the specified spoke.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The amount of drawn shares.
  function getSpokeDrawnShares(uint256 assetId, address spoke) external view returns (uint256);

  /// @notice Returns the information regarding premium shares of the specified asset for the specified spoke.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The amount of premium shares.
  /// @return The premium offset, expressed in asset units and scaled by RAY.
  function getSpokePremiumData(
    uint256 assetId,
    address spoke
  ) external view returns (uint256, int256);

  /// @notice Returns the amount of a given spoke's deficit with full precision for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The amount of deficit, expressed in asset units and scaled by RAY.
  function getSpokeDeficitRay(uint256 assetId, address spoke) external view returns (uint256);
}

// src/interfaces/IMulticall.sol

/// @title IMulticall
/// @author Aave Labs
/// @notice Minimal interface for Multicall.
interface IMulticall {
  /// @notice Call multiple functions in the current contract and return the data from each if they all succeed.
  /// @param data The encoded function data for each of the calls to make to this contract.
  /// @return results The results from each of the calls passed in via data.
  function multicall(bytes[] calldata data) external returns (bytes[] memory);
}

// src/interfaces/INoncesKeyed.sol

interface INoncesKeyed {
  /// @notice Thrown when nonce being consumed does not match `currentNonce` for `account`.
  error InvalidAccountNonce(address account, uint256 currentNonce);

  /// @notice Allows caller to revoke their next sequential nonce at specified `key`.
  /// @dev This does not invalidate nonce at other `key`s namespace.
  /// @param key The key which specifies namespace of the nonce.
  /// @return keyNonce The revoked key-prefixed nonce.
  function useNonce(uint192 key) external returns (uint256 keyNonce);

  /// @notice Returns the next unused nonce for an address and key. Result contains the key prefix.
  /// @param owner The address of the nonce owner.
  /// @param key The key which specifies namespace of the nonce.
  /// @return keyNonce The first 24 bytes are for the key, & the last 8 bytes for the nonce.
  function nonces(address owner, uint192 key) external view returns (uint256 keyNonce);
}

// src/spoke/interfaces/IPriceOracle.sol

/// @title IPriceOracle
/// @author Aave Labs
/// @notice Basic interface for any price oracle.
/// @dev All prices must use the same number of decimals as the oracle and should be returned in the same currency.
interface IPriceOracle {
  /// @dev Reverts if the caller is not the Spoke.
  error OnlySpoke();

  /// @notice Returns the address of the Spoke.
  function spoke() external view returns (address);

  /// @notice Returns the number of decimals used to return prices.
  function decimals() external view returns (uint8);

  /// @notice Returns the reserve price with `decimals` precision.
  /// @dev Reverts if the price is not greater than 0.
  /// @param reserveId The identifier of the reserve.
  /// @return The price of the reserve.
  function getReservePrice(uint256 reserveId) external view returns (uint256);
}

// src/dependencies/solady/LibBit.sol

// trimmed https://github.com/Vectorized/solady/blob/ba711c9fa6a2dc7b2b7707f7fe136b5133379c03/src/utils/LibBit.sol

/// @notice Library for bit twiddling and boolean operations.
/// @author Solady (https://github.com/vectorized/solady/blob/main/src/utils/LibBit.sol)
/// @author Inspired by (https://graphics.stanford.edu/~seander/bithacks.html)
library LibBit {
  /// @dev Returns the number of set bits in `x`.
  function popCount(uint256 x) internal pure returns (uint256 c) {
    /// @solidity memory-safe-assembly
    assembly {
      let max := not(0)
      let isMax := eq(x, max)
      x := sub(x, and(shr(1, x), div(max, 3)))
      x := add(and(x, div(max, 5)), and(shr(2, x), div(max, 5)))
      x := and(add(x, shr(4, x)), div(max, 17))
      c := or(shl(8, isMax), shr(248, mul(x, div(max, 255))))
    }
  }

  /// @dev Find last set.
  /// Returns the index of the most significant bit of `x`,
  /// counting from the least significant bit position.
  /// If `x` is zero, returns 256.
  function fls(uint256 x) internal pure returns (uint256 r) {
    /// @solidity memory-safe-assembly
    assembly {
      r := or(shl(8, iszero(x)), shl(7, lt(0xffffffffffffffffffffffffffffffff, x)))
      r := or(r, shl(6, lt(0xffffffffffffffff, shr(r, x))))
      r := or(r, shl(5, lt(0xffffffff, shr(r, x))))
      r := or(r, shl(4, lt(0xffff, shr(r, x))))
      r := or(r, shl(3, lt(0xff, shr(r, x))))
      // forgefmt: disable-next-item
      r := or(
        r,
        byte(
          and(0x1f, shr(shr(r, x), 0x8421084210842108cc6318c6db6d54be)),
          0x0706060506020504060203020504030106050205030304010505030400000000
        )
      )
    }
  }
}

// src/dependencies/openzeppelin/Panic.sol

// OpenZeppelin Contracts (last updated v5.1.0) (utils/Panic.sol)

/**
 * @dev Helper library for emitting standardized panic codes.
 *
 * ```solidity
 * contract Example {
 *      using Panic for uint256;
 *
 *      // Use any of the declared internal constants
 *      function foo() { Panic.GENERIC.panic(); }
 *
 *      // Alternatively
 *      function foo() { Panic.panic(Panic.GENERIC); }
 * }
 * ```
 *
 * Follows the list from https://github.com/ethereum/solidity/blob/v0.8.24/libsolutil/ErrorCodes.h[libsolutil].
 *
 * _Available since v5.1._
 */
// slither-disable-next-line unused-state
library Panic {
  /// @dev generic / unspecified error
  uint256 internal constant GENERIC = 0x00;
  /// @dev used by the assert() builtin
  uint256 internal constant ASSERT = 0x01;
  /// @dev arithmetic underflow or overflow
  uint256 internal constant UNDER_OVERFLOW = 0x11;
  /// @dev division or modulo by zero
  uint256 internal constant DIVISION_BY_ZERO = 0x12;
  /// @dev enum conversion error
  uint256 internal constant ENUM_CONVERSION_ERROR = 0x21;
  /// @dev invalid encoding in storage
  uint256 internal constant STORAGE_ENCODING_ERROR = 0x22;
  /// @dev empty array pop
  uint256 internal constant EMPTY_ARRAY_POP = 0x31;
  /// @dev array out of bounds access
  uint256 internal constant ARRAY_OUT_OF_BOUNDS = 0x32;
  /// @dev resource error (too large allocation or too large array)
  uint256 internal constant RESOURCE_ERROR = 0x41;
  /// @dev calling invalid internal function
  uint256 internal constant INVALID_INTERNAL_FUNCTION = 0x51;

  /// @dev Reverts with a panic code. Recommended to use with
  /// the internal constants with predefined codes.
  function panic(uint256 code) internal pure {
    assembly ('memory-safe') {
      mstore(0x00, 0x4e487b71)
      mstore(0x20, code)
      revert(0x1c, 0x24)
    }
  }
}

// src/libraries/math/PercentageMath.sol

/// @title PercentageMath library
/// @author Aave Labs
/// @notice Provides functions to perform percentage calculations with explicit rounding.
/// @dev Percentages are defined by default with 2 decimals of precision (100.00). The precision is indicated by `PERCENTAGE_FACTOR`.
library PercentageMath {
  // Percentage factor expressed in BPS (100.00%)
  uint256 internal constant PERCENTAGE_FACTOR = 1e4;

  /// @notice Executes a percentage multiplication, rounded down.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return result = floor(value * percentage / PERCENTAGE_FACTOR)
  function percentMulDown(
    uint256 value,
    uint256 percentage
  ) internal pure returns (uint256 result) {
    // to avoid overflow, value <= type(uint256).max / percentage
    assembly ('memory-safe') {
      if iszero(or(iszero(percentage), iszero(gt(value, div(not(0), percentage))))) {
        revert(0, 0)
      }

      result := div(mul(value, percentage), PERCENTAGE_FACTOR)
    }
  }

  /// @notice Executes a percentage multiplication, rounded up.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return result = ceil(value * percentage / PERCENTAGE_FACTOR)
  function percentMulUp(uint256 value, uint256 percentage) internal pure returns (uint256 result) {
    // to avoid overflow, value <= type(uint256).max / percentage
    assembly ('memory-safe') {
      if iszero(or(iszero(percentage), iszero(gt(value, div(not(0), percentage))))) {
        revert(0, 0)
      }
      result := mul(value, percentage)

      // Add 1 if (value * percentage) % PERCENTAGE_FACTOR > 0 to round up the division of (value * percentage) by PERCENTAGE_FACTOR
      result := add(div(result, PERCENTAGE_FACTOR), gt(mod(result, PERCENTAGE_FACTOR), 0))
    }
  }

  /// @notice Executes a percentage division, rounded down.
  /// @dev Reverts if division by zero or intermediate multiplication overflows.
  /// @return result = floor(value * PERCENTAGE_FACTOR / percentage)
  function percentDivDown(
    uint256 value,
    uint256 percentage
  ) internal pure returns (uint256 result) {
    // to avoid overflow, value <= type(uint256).max / PERCENTAGE_FACTOR
    assembly ('memory-safe') {
      if or(iszero(percentage), iszero(iszero(gt(value, div(not(0), PERCENTAGE_FACTOR))))) {
        revert(0, 0)
      }

      result := div(mul(value, PERCENTAGE_FACTOR), percentage)
    }
  }

  /// @notice Executes a percentage division, rounded up.
  /// @dev Reverts if division by zero or intermediate multiplication overflows.
  /// @return result = ceil(value * PERCENTAGE_FACTOR / percentage)
  function percentDivUp(uint256 value, uint256 percentage) internal pure returns (uint256 result) {
    // to avoid overflow, value <= type(uint256).max / PERCENTAGE_FACTOR
    assembly ('memory-safe') {
      if or(iszero(percentage), iszero(iszero(gt(value, div(not(0), PERCENTAGE_FACTOR))))) {
        revert(0, 0)
      }
      result := mul(value, PERCENTAGE_FACTOR)

      // Add 1 if (value * PERCENTAGE_FACTOR) % percentage > 0 to round up the division of (value * PERCENTAGE_FACTOR) by percentage
      result := add(div(result, percentage), gt(mod(result, percentage), 0))
    }
  }

  /// @notice Truncates number from BPS precision, rounding down.
  function fromBpsDown(uint256 value) internal pure returns (uint256) {
    return value / PERCENTAGE_FACTOR;
  }
}

// src/dependencies/openzeppelin/SafeCast.sol

// OpenZeppelin Contracts (last updated v5.1.0) (utils/math/SafeCast.sol)
// This file was procedurally generated from scripts/generate/templates/SafeCast.js.

/**
 * @dev Wrappers over Solidity's uintXX/intXX/bool casting operators with added overflow
 * checks.
 *
 * Downcasting from uint256/int256 in Solidity does not revert on overflow. This can
 * easily result in undesired exploitation or bugs, since developers usually
 * assume that overflows raise errors. `SafeCast` restores this intuition by
 * reverting the transaction when such an operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeCast {
  /**
   * @dev Value doesn't fit in an uint of `bits` size.
   */
  error SafeCastOverflowedUintDowncast(uint8 bits, uint256 value);

  /**
   * @dev An int value doesn't fit in an uint of `bits` size.
   */
  error SafeCastOverflowedIntToUint(int256 value);

  /**
   * @dev Value doesn't fit in an int of `bits` size.
   */
  error SafeCastOverflowedIntDowncast(uint8 bits, int256 value);

  /**
   * @dev An uint value doesn't fit in an int of `bits` size.
   */
  error SafeCastOverflowedUintToInt(uint256 value);

  /**
   * @dev Returns the downcasted uint248 from uint256, reverting on
   * overflow (when the input is greater than largest uint248).
   *
   * Counterpart to Solidity's `uint248` operator.
   *
   * Requirements:
   *
   * - input must fit into 248 bits
   */
  function toUint248(uint256 value) internal pure returns (uint248) {
    if (value > type(uint248).max) {
      revert SafeCastOverflowedUintDowncast(248, value);
    }
    return uint248(value);
  }

  /**
   * @dev Returns the downcasted uint240 from uint256, reverting on
   * overflow (when the input is greater than largest uint240).
   *
   * Counterpart to Solidity's `uint240` operator.
   *
   * Requirements:
   *
   * - input must fit into 240 bits
   */
  function toUint240(uint256 value) internal pure returns (uint240) {
    if (value > type(uint240).max) {
      revert SafeCastOverflowedUintDowncast(240, value);
    }
    return uint240(value);
  }

  /**
   * @dev Returns the downcasted uint232 from uint256, reverting on
   * overflow (when the input is greater than largest uint232).
   *
   * Counterpart to Solidity's `uint232` operator.
   *
   * Requirements:
   *
   * - input must fit into 232 bits
   */
  function toUint232(uint256 value) internal pure returns (uint232) {
    if (value > type(uint232).max) {
      revert SafeCastOverflowedUintDowncast(232, value);
    }
    return uint232(value);
  }

  /**
   * @dev Returns the downcasted uint224 from uint256, reverting on
   * overflow (when the input is greater than largest uint224).
   *
   * Counterpart to Solidity's `uint224` operator.
   *
   * Requirements:
   *
   * - input must fit into 224 bits
   */
  function toUint224(uint256 value) internal pure returns (uint224) {
    if (value > type(uint224).max) {
      revert SafeCastOverflowedUintDowncast(224, value);
    }
    return uint224(value);
  }

  /**
   * @dev Returns the downcasted uint216 from uint256, reverting on
   * overflow (when the input is greater than largest uint216).
   *
   * Counterpart to Solidity's `uint216` operator.
   *
   * Requirements:
   *
   * - input must fit into 216 bits
   */
  function toUint216(uint256 value) internal pure returns (uint216) {
    if (value > type(uint216).max) {
      revert SafeCastOverflowedUintDowncast(216, value);
    }
    return uint216(value);
  }

  /**
   * @dev Returns the downcasted uint208 from uint256, reverting on
   * overflow (when the input is greater than largest uint208).
   *
   * Counterpart to Solidity's `uint208` operator.
   *
   * Requirements:
   *
   * - input must fit into 208 bits
   */
  function toUint208(uint256 value) internal pure returns (uint208) {
    if (value > type(uint208).max) {
      revert SafeCastOverflowedUintDowncast(208, value);
    }
    return uint208(value);
  }

  /**
   * @dev Returns the downcasted uint200 from uint256, reverting on
   * overflow (when the input is greater than largest uint200).
   *
   * Counterpart to Solidity's `uint200` operator.
   *
   * Requirements:
   *
   * - input must fit into 200 bits
   */
  function toUint200(uint256 value) internal pure returns (uint200) {
    if (value > type(uint200).max) {
      revert SafeCastOverflowedUintDowncast(200, value);
    }
    return uint200(value);
  }

  /**
   * @dev Returns the downcasted uint192 from uint256, reverting on
   * overflow (when the input is greater than largest uint192).
   *
   * Counterpart to Solidity's `uint192` operator.
   *
   * Requirements:
   *
   * - input must fit into 192 bits
   */
  function toUint192(uint256 value) internal pure returns (uint192) {
    if (value > type(uint192).max) {
      revert SafeCastOverflowedUintDowncast(192, value);
    }
    return uint192(value);
  }

  /**
   * @dev Returns the downcasted uint184 from uint256, reverting on
   * overflow (when the input is greater than largest uint184).
   *
   * Counterpart to Solidity's `uint184` operator.
   *
   * Requirements:
   *
   * - input must fit into 184 bits
   */
  function toUint184(uint256 value) internal pure returns (uint184) {
    if (value > type(uint184).max) {
      revert SafeCastOverflowedUintDowncast(184, value);
    }
    return uint184(value);
  }

  /**
   * @dev Returns the downcasted uint176 from uint256, reverting on
   * overflow (when the input is greater than largest uint176).
   *
   * Counterpart to Solidity's `uint176` operator.
   *
   * Requirements:
   *
   * - input must fit into 176 bits
   */
  function toUint176(uint256 value) internal pure returns (uint176) {
    if (value > type(uint176).max) {
      revert SafeCastOverflowedUintDowncast(176, value);
    }
    return uint176(value);
  }

  /**
   * @dev Returns the downcasted uint168 from uint256, reverting on
   * overflow (when the input is greater than largest uint168).
   *
   * Counterpart to Solidity's `uint168` operator.
   *
   * Requirements:
   *
   * - input must fit into 168 bits
   */
  function toUint168(uint256 value) internal pure returns (uint168) {
    if (value > type(uint168).max) {
      revert SafeCastOverflowedUintDowncast(168, value);
    }
    return uint168(value);
  }

  /**
   * @dev Returns the downcasted uint160 from uint256, reverting on
   * overflow (when the input is greater than largest uint160).
   *
   * Counterpart to Solidity's `uint160` operator.
   *
   * Requirements:
   *
   * - input must fit into 160 bits
   */
  function toUint160(uint256 value) internal pure returns (uint160) {
    if (value > type(uint160).max) {
      revert SafeCastOverflowedUintDowncast(160, value);
    }
    return uint160(value);
  }

  /**
   * @dev Returns the downcasted uint152 from uint256, reverting on
   * overflow (when the input is greater than largest uint152).
   *
   * Counterpart to Solidity's `uint152` operator.
   *
   * Requirements:
   *
   * - input must fit into 152 bits
   */
  function toUint152(uint256 value) internal pure returns (uint152) {
    if (value > type(uint152).max) {
      revert SafeCastOverflowedUintDowncast(152, value);
    }
    return uint152(value);
  }

  /**
   * @dev Returns the downcasted uint144 from uint256, reverting on
   * overflow (when the input is greater than largest uint144).
   *
   * Counterpart to Solidity's `uint144` operator.
   *
   * Requirements:
   *
   * - input must fit into 144 bits
   */
  function toUint144(uint256 value) internal pure returns (uint144) {
    if (value > type(uint144).max) {
      revert SafeCastOverflowedUintDowncast(144, value);
    }
    return uint144(value);
  }

  /**
   * @dev Returns the downcasted uint136 from uint256, reverting on
   * overflow (when the input is greater than largest uint136).
   *
   * Counterpart to Solidity's `uint136` operator.
   *
   * Requirements:
   *
   * - input must fit into 136 bits
   */
  function toUint136(uint256 value) internal pure returns (uint136) {
    if (value > type(uint136).max) {
      revert SafeCastOverflowedUintDowncast(136, value);
    }
    return uint136(value);
  }

  /**
   * @dev Returns the downcasted uint128 from uint256, reverting on
   * overflow (when the input is greater than largest uint128).
   *
   * Counterpart to Solidity's `uint128` operator.
   *
   * Requirements:
   *
   * - input must fit into 128 bits
   */
  function toUint128(uint256 value) internal pure returns (uint128) {
    if (value > type(uint128).max) {
      revert SafeCastOverflowedUintDowncast(128, value);
    }
    return uint128(value);
  }

  /**
   * @dev Returns the downcasted uint120 from uint256, reverting on
   * overflow (when the input is greater than largest uint120).
   *
   * Counterpart to Solidity's `uint120` operator.
   *
   * Requirements:
   *
   * - input must fit into 120 bits
   */
  function toUint120(uint256 value) internal pure returns (uint120) {
    if (value > type(uint120).max) {
      revert SafeCastOverflowedUintDowncast(120, value);
    }
    return uint120(value);
  }

  /**
   * @dev Returns the downcasted uint112 from uint256, reverting on
   * overflow (when the input is greater than largest uint112).
   *
   * Counterpart to Solidity's `uint112` operator.
   *
   * Requirements:
   *
   * - input must fit into 112 bits
   */
  function toUint112(uint256 value) internal pure returns (uint112) {
    if (value > type(uint112).max) {
      revert SafeCastOverflowedUintDowncast(112, value);
    }
    return uint112(value);
  }

  /**
   * @dev Returns the downcasted uint104 from uint256, reverting on
   * overflow (when the input is greater than largest uint104).
   *
   * Counterpart to Solidity's `uint104` operator.
   *
   * Requirements:
   *
   * - input must fit into 104 bits
   */
  function toUint104(uint256 value) internal pure returns (uint104) {
    if (value > type(uint104).max) {
      revert SafeCastOverflowedUintDowncast(104, value);
    }
    return uint104(value);
  }

  /**
   * @dev Returns the downcasted uint96 from uint256, reverting on
   * overflow (when the input is greater than largest uint96).
   *
   * Counterpart to Solidity's `uint96` operator.
   *
   * Requirements:
   *
   * - input must fit into 96 bits
   */
  function toUint96(uint256 value) internal pure returns (uint96) {
    if (value > type(uint96).max) {
      revert SafeCastOverflowedUintDowncast(96, value);
    }
    return uint96(value);
  }

  /**
   * @dev Returns the downcasted uint88 from uint256, reverting on
   * overflow (when the input is greater than largest uint88).
   *
   * Counterpart to Solidity's `uint88` operator.
   *
   * Requirements:
   *
   * - input must fit into 88 bits
   */
  function toUint88(uint256 value) internal pure returns (uint88) {
    if (value > type(uint88).max) {
      revert SafeCastOverflowedUintDowncast(88, value);
    }
    return uint88(value);
  }

  /**
   * @dev Returns the downcasted uint80 from uint256, reverting on
   * overflow (when the input is greater than largest uint80).
   *
   * Counterpart to Solidity's `uint80` operator.
   *
   * Requirements:
   *
   * - input must fit into 80 bits
   */
  function toUint80(uint256 value) internal pure returns (uint80) {
    if (value > type(uint80).max) {
      revert SafeCastOverflowedUintDowncast(80, value);
    }
    return uint80(value);
  }

  /**
   * @dev Returns the downcasted uint72 from uint256, reverting on
   * overflow (when the input is greater than largest uint72).
   *
   * Counterpart to Solidity's `uint72` operator.
   *
   * Requirements:
   *
   * - input must fit into 72 bits
   */
  function toUint72(uint256 value) internal pure returns (uint72) {
    if (value > type(uint72).max) {
      revert SafeCastOverflowedUintDowncast(72, value);
    }
    return uint72(value);
  }

  /**
   * @dev Returns the downcasted uint64 from uint256, reverting on
   * overflow (when the input is greater than largest uint64).
   *
   * Counterpart to Solidity's `uint64` operator.
   *
   * Requirements:
   *
   * - input must fit into 64 bits
   */
  function toUint64(uint256 value) internal pure returns (uint64) {
    if (value > type(uint64).max) {
      revert SafeCastOverflowedUintDowncast(64, value);
    }
    return uint64(value);
  }

  /**
   * @dev Returns the downcasted uint56 from uint256, reverting on
   * overflow (when the input is greater than largest uint56).
   *
   * Counterpart to Solidity's `uint56` operator.
   *
   * Requirements:
   *
   * - input must fit into 56 bits
   */
  function toUint56(uint256 value) internal pure returns (uint56) {
    if (value > type(uint56).max) {
      revert SafeCastOverflowedUintDowncast(56, value);
    }
    return uint56(value);
  }

  /**
   * @dev Returns the downcasted uint48 from uint256, reverting on
   * overflow (when the input is greater than largest uint48).
   *
   * Counterpart to Solidity's `uint48` operator.
   *
   * Requirements:
   *
   * - input must fit into 48 bits
   */
  function toUint48(uint256 value) internal pure returns (uint48) {
    if (value > type(uint48).max) {
      revert SafeCastOverflowedUintDowncast(48, value);
    }
    return uint48(value);
  }

  /**
   * @dev Returns the downcasted uint40 from uint256, reverting on
   * overflow (when the input is greater than largest uint40).
   *
   * Counterpart to Solidity's `uint40` operator.
   *
   * Requirements:
   *
   * - input must fit into 40 bits
   */
  function toUint40(uint256 value) internal pure returns (uint40) {
    if (value > type(uint40).max) {
      revert SafeCastOverflowedUintDowncast(40, value);
    }
    return uint40(value);
  }

  /**
   * @dev Returns the downcasted uint32 from uint256, reverting on
   * overflow (when the input is greater than largest uint32).
   *
   * Counterpart to Solidity's `uint32` operator.
   *
   * Requirements:
   *
   * - input must fit into 32 bits
   */
  function toUint32(uint256 value) internal pure returns (uint32) {
    if (value > type(uint32).max) {
      revert SafeCastOverflowedUintDowncast(32, value);
    }
    return uint32(value);
  }

  /**
   * @dev Returns the downcasted uint24 from uint256, reverting on
   * overflow (when the input is greater than largest uint24).
   *
   * Counterpart to Solidity's `uint24` operator.
   *
   * Requirements:
   *
   * - input must fit into 24 bits
   */
  function toUint24(uint256 value) internal pure returns (uint24) {
    if (value > type(uint24).max) {
      revert SafeCastOverflowedUintDowncast(24, value);
    }
    return uint24(value);
  }

  /**
   * @dev Returns the downcasted uint16 from uint256, reverting on
   * overflow (when the input is greater than largest uint16).
   *
   * Counterpart to Solidity's `uint16` operator.
   *
   * Requirements:
   *
   * - input must fit into 16 bits
   */
  function toUint16(uint256 value) internal pure returns (uint16) {
    if (value > type(uint16).max) {
      revert SafeCastOverflowedUintDowncast(16, value);
    }
    return uint16(value);
  }

  /**
   * @dev Returns the downcasted uint8 from uint256, reverting on
   * overflow (when the input is greater than largest uint8).
   *
   * Counterpart to Solidity's `uint8` operator.
   *
   * Requirements:
   *
   * - input must fit into 8 bits
   */
  function toUint8(uint256 value) internal pure returns (uint8) {
    if (value > type(uint8).max) {
      revert SafeCastOverflowedUintDowncast(8, value);
    }
    return uint8(value);
  }

  /**
   * @dev Converts a signed int256 into an unsigned uint256.
   *
   * Requirements:
   *
   * - input must be greater than or equal to 0.
   */
  function toUint256(int256 value) internal pure returns (uint256) {
    if (value < 0) {
      revert SafeCastOverflowedIntToUint(value);
    }
    return uint256(value);
  }

  /**
   * @dev Returns the downcasted int248 from int256, reverting on
   * overflow (when the input is less than smallest int248 or
   * greater than largest int248).
   *
   * Counterpart to Solidity's `int248` operator.
   *
   * Requirements:
   *
   * - input must fit into 248 bits
   */
  function toInt248(int256 value) internal pure returns (int248 downcasted) {
    downcasted = int248(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(248, value);
    }
  }

  /**
   * @dev Returns the downcasted int240 from int256, reverting on
   * overflow (when the input is less than smallest int240 or
   * greater than largest int240).
   *
   * Counterpart to Solidity's `int240` operator.
   *
   * Requirements:
   *
   * - input must fit into 240 bits
   */
  function toInt240(int256 value) internal pure returns (int240 downcasted) {
    downcasted = int240(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(240, value);
    }
  }

  /**
   * @dev Returns the downcasted int232 from int256, reverting on
   * overflow (when the input is less than smallest int232 or
   * greater than largest int232).
   *
   * Counterpart to Solidity's `int232` operator.
   *
   * Requirements:
   *
   * - input must fit into 232 bits
   */
  function toInt232(int256 value) internal pure returns (int232 downcasted) {
    downcasted = int232(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(232, value);
    }
  }

  /**
   * @dev Returns the downcasted int224 from int256, reverting on
   * overflow (when the input is less than smallest int224 or
   * greater than largest int224).
   *
   * Counterpart to Solidity's `int224` operator.
   *
   * Requirements:
   *
   * - input must fit into 224 bits
   */
  function toInt224(int256 value) internal pure returns (int224 downcasted) {
    downcasted = int224(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(224, value);
    }
  }

  /**
   * @dev Returns the downcasted int216 from int256, reverting on
   * overflow (when the input is less than smallest int216 or
   * greater than largest int216).
   *
   * Counterpart to Solidity's `int216` operator.
   *
   * Requirements:
   *
   * - input must fit into 216 bits
   */
  function toInt216(int256 value) internal pure returns (int216 downcasted) {
    downcasted = int216(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(216, value);
    }
  }

  /**
   * @dev Returns the downcasted int208 from int256, reverting on
   * overflow (when the input is less than smallest int208 or
   * greater than largest int208).
   *
   * Counterpart to Solidity's `int208` operator.
   *
   * Requirements:
   *
   * - input must fit into 208 bits
   */
  function toInt208(int256 value) internal pure returns (int208 downcasted) {
    downcasted = int208(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(208, value);
    }
  }

  /**
   * @dev Returns the downcasted int200 from int256, reverting on
   * overflow (when the input is less than smallest int200 or
   * greater than largest int200).
   *
   * Counterpart to Solidity's `int200` operator.
   *
   * Requirements:
   *
   * - input must fit into 200 bits
   */
  function toInt200(int256 value) internal pure returns (int200 downcasted) {
    downcasted = int200(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(200, value);
    }
  }

  /**
   * @dev Returns the downcasted int192 from int256, reverting on
   * overflow (when the input is less than smallest int192 or
   * greater than largest int192).
   *
   * Counterpart to Solidity's `int192` operator.
   *
   * Requirements:
   *
   * - input must fit into 192 bits
   */
  function toInt192(int256 value) internal pure returns (int192 downcasted) {
    downcasted = int192(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(192, value);
    }
  }

  /**
   * @dev Returns the downcasted int184 from int256, reverting on
   * overflow (when the input is less than smallest int184 or
   * greater than largest int184).
   *
   * Counterpart to Solidity's `int184` operator.
   *
   * Requirements:
   *
   * - input must fit into 184 bits
   */
  function toInt184(int256 value) internal pure returns (int184 downcasted) {
    downcasted = int184(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(184, value);
    }
  }

  /**
   * @dev Returns the downcasted int176 from int256, reverting on
   * overflow (when the input is less than smallest int176 or
   * greater than largest int176).
   *
   * Counterpart to Solidity's `int176` operator.
   *
   * Requirements:
   *
   * - input must fit into 176 bits
   */
  function toInt176(int256 value) internal pure returns (int176 downcasted) {
    downcasted = int176(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(176, value);
    }
  }

  /**
   * @dev Returns the downcasted int168 from int256, reverting on
   * overflow (when the input is less than smallest int168 or
   * greater than largest int168).
   *
   * Counterpart to Solidity's `int168` operator.
   *
   * Requirements:
   *
   * - input must fit into 168 bits
   */
  function toInt168(int256 value) internal pure returns (int168 downcasted) {
    downcasted = int168(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(168, value);
    }
  }

  /**
   * @dev Returns the downcasted int160 from int256, reverting on
   * overflow (when the input is less than smallest int160 or
   * greater than largest int160).
   *
   * Counterpart to Solidity's `int160` operator.
   *
   * Requirements:
   *
   * - input must fit into 160 bits
   */
  function toInt160(int256 value) internal pure returns (int160 downcasted) {
    downcasted = int160(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(160, value);
    }
  }

  /**
   * @dev Returns the downcasted int152 from int256, reverting on
   * overflow (when the input is less than smallest int152 or
   * greater than largest int152).
   *
   * Counterpart to Solidity's `int152` operator.
   *
   * Requirements:
   *
   * - input must fit into 152 bits
   */
  function toInt152(int256 value) internal pure returns (int152 downcasted) {
    downcasted = int152(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(152, value);
    }
  }

  /**
   * @dev Returns the downcasted int144 from int256, reverting on
   * overflow (when the input is less than smallest int144 or
   * greater than largest int144).
   *
   * Counterpart to Solidity's `int144` operator.
   *
   * Requirements:
   *
   * - input must fit into 144 bits
   */
  function toInt144(int256 value) internal pure returns (int144 downcasted) {
    downcasted = int144(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(144, value);
    }
  }

  /**
   * @dev Returns the downcasted int136 from int256, reverting on
   * overflow (when the input is less than smallest int136 or
   * greater than largest int136).
   *
   * Counterpart to Solidity's `int136` operator.
   *
   * Requirements:
   *
   * - input must fit into 136 bits
   */
  function toInt136(int256 value) internal pure returns (int136 downcasted) {
    downcasted = int136(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(136, value);
    }
  }

  /**
   * @dev Returns the downcasted int128 from int256, reverting on
   * overflow (when the input is less than smallest int128 or
   * greater than largest int128).
   *
   * Counterpart to Solidity's `int128` operator.
   *
   * Requirements:
   *
   * - input must fit into 128 bits
   */
  function toInt128(int256 value) internal pure returns (int128 downcasted) {
    downcasted = int128(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(128, value);
    }
  }

  /**
   * @dev Returns the downcasted int120 from int256, reverting on
   * overflow (when the input is less than smallest int120 or
   * greater than largest int120).
   *
   * Counterpart to Solidity's `int120` operator.
   *
   * Requirements:
   *
   * - input must fit into 120 bits
   */
  function toInt120(int256 value) internal pure returns (int120 downcasted) {
    downcasted = int120(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(120, value);
    }
  }

  /**
   * @dev Returns the downcasted int112 from int256, reverting on
   * overflow (when the input is less than smallest int112 or
   * greater than largest int112).
   *
   * Counterpart to Solidity's `int112` operator.
   *
   * Requirements:
   *
   * - input must fit into 112 bits
   */
  function toInt112(int256 value) internal pure returns (int112 downcasted) {
    downcasted = int112(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(112, value);
    }
  }

  /**
   * @dev Returns the downcasted int104 from int256, reverting on
   * overflow (when the input is less than smallest int104 or
   * greater than largest int104).
   *
   * Counterpart to Solidity's `int104` operator.
   *
   * Requirements:
   *
   * - input must fit into 104 bits
   */
  function toInt104(int256 value) internal pure returns (int104 downcasted) {
    downcasted = int104(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(104, value);
    }
  }

  /**
   * @dev Returns the downcasted int96 from int256, reverting on
   * overflow (when the input is less than smallest int96 or
   * greater than largest int96).
   *
   * Counterpart to Solidity's `int96` operator.
   *
   * Requirements:
   *
   * - input must fit into 96 bits
   */
  function toInt96(int256 value) internal pure returns (int96 downcasted) {
    downcasted = int96(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(96, value);
    }
  }

  /**
   * @dev Returns the downcasted int88 from int256, reverting on
   * overflow (when the input is less than smallest int88 or
   * greater than largest int88).
   *
   * Counterpart to Solidity's `int88` operator.
   *
   * Requirements:
   *
   * - input must fit into 88 bits
   */
  function toInt88(int256 value) internal pure returns (int88 downcasted) {
    downcasted = int88(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(88, value);
    }
  }

  /**
   * @dev Returns the downcasted int80 from int256, reverting on
   * overflow (when the input is less than smallest int80 or
   * greater than largest int80).
   *
   * Counterpart to Solidity's `int80` operator.
   *
   * Requirements:
   *
   * - input must fit into 80 bits
   */
  function toInt80(int256 value) internal pure returns (int80 downcasted) {
    downcasted = int80(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(80, value);
    }
  }

  /**
   * @dev Returns the downcasted int72 from int256, reverting on
   * overflow (when the input is less than smallest int72 or
   * greater than largest int72).
   *
   * Counterpart to Solidity's `int72` operator.
   *
   * Requirements:
   *
   * - input must fit into 72 bits
   */
  function toInt72(int256 value) internal pure returns (int72 downcasted) {
    downcasted = int72(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(72, value);
    }
  }

  /**
   * @dev Returns the downcasted int64 from int256, reverting on
   * overflow (when the input is less than smallest int64 or
   * greater than largest int64).
   *
   * Counterpart to Solidity's `int64` operator.
   *
   * Requirements:
   *
   * - input must fit into 64 bits
   */
  function toInt64(int256 value) internal pure returns (int64 downcasted) {
    downcasted = int64(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(64, value);
    }
  }

  /**
   * @dev Returns the downcasted int56 from int256, reverting on
   * overflow (when the input is less than smallest int56 or
   * greater than largest int56).
   *
   * Counterpart to Solidity's `int56` operator.
   *
   * Requirements:
   *
   * - input must fit into 56 bits
   */
  function toInt56(int256 value) internal pure returns (int56 downcasted) {
    downcasted = int56(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(56, value);
    }
  }

  /**
   * @dev Returns the downcasted int48 from int256, reverting on
   * overflow (when the input is less than smallest int48 or
   * greater than largest int48).
   *
   * Counterpart to Solidity's `int48` operator.
   *
   * Requirements:
   *
   * - input must fit into 48 bits
   */
  function toInt48(int256 value) internal pure returns (int48 downcasted) {
    downcasted = int48(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(48, value);
    }
  }

  /**
   * @dev Returns the downcasted int40 from int256, reverting on
   * overflow (when the input is less than smallest int40 or
   * greater than largest int40).
   *
   * Counterpart to Solidity's `int40` operator.
   *
   * Requirements:
   *
   * - input must fit into 40 bits
   */
  function toInt40(int256 value) internal pure returns (int40 downcasted) {
    downcasted = int40(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(40, value);
    }
  }

  /**
   * @dev Returns the downcasted int32 from int256, reverting on
   * overflow (when the input is less than smallest int32 or
   * greater than largest int32).
   *
   * Counterpart to Solidity's `int32` operator.
   *
   * Requirements:
   *
   * - input must fit into 32 bits
   */
  function toInt32(int256 value) internal pure returns (int32 downcasted) {
    downcasted = int32(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(32, value);
    }
  }

  /**
   * @dev Returns the downcasted int24 from int256, reverting on
   * overflow (when the input is less than smallest int24 or
   * greater than largest int24).
   *
   * Counterpart to Solidity's `int24` operator.
   *
   * Requirements:
   *
   * - input must fit into 24 bits
   */
  function toInt24(int256 value) internal pure returns (int24 downcasted) {
    downcasted = int24(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(24, value);
    }
  }

  /**
   * @dev Returns the downcasted int16 from int256, reverting on
   * overflow (when the input is less than smallest int16 or
   * greater than largest int16).
   *
   * Counterpart to Solidity's `int16` operator.
   *
   * Requirements:
   *
   * - input must fit into 16 bits
   */
  function toInt16(int256 value) internal pure returns (int16 downcasted) {
    downcasted = int16(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(16, value);
    }
  }

  /**
   * @dev Returns the downcasted int8 from int256, reverting on
   * overflow (when the input is less than smallest int8 or
   * greater than largest int8).
   *
   * Counterpart to Solidity's `int8` operator.
   *
   * Requirements:
   *
   * - input must fit into 8 bits
   */
  function toInt8(int256 value) internal pure returns (int8 downcasted) {
    downcasted = int8(value);
    if (downcasted != value) {
      revert SafeCastOverflowedIntDowncast(8, value);
    }
  }

  /**
   * @dev Converts an unsigned uint256 into a signed int256.
   *
   * Requirements:
   *
   * - input must be less than or equal to maxInt256.
   */
  function toInt256(uint256 value) internal pure returns (int256) {
    // Note: Unsafe cast below is okay because `type(int256).max` is guaranteed to be positive
    if (value > uint256(type(int256).max)) {
      revert SafeCastOverflowedUintToInt(value);
    }
    return int256(value);
  }

  /**
   * @dev Cast a boolean (false or true) to a uint256 (0 or 1) with no jump.
   */
  function toUint(bool b) internal pure returns (uint256 u) {
    assembly ('memory-safe') {
      u := iszero(iszero(b))
    }
  }
}

// src/libraries/math/WadRayMath.sol

/// @title WadRayMath library
/// @author Aave Labs
/// @notice Provides utility functions to work with WAD and RAY units with explicit rounding.
library WadRayMath {
  uint256 internal constant WAD_DECIMALS = 18;
  uint256 internal constant WAD = 1e18;
  uint256 internal constant RAY = 1e27;
  uint256 internal constant PERCENTAGE_FACTOR = 1e4;

  /// @notice Multiplies two WAD numbers, rounding down.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return c = floor(a * b / WAD), expressed in WAD.
  function wadMulDown(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / b
      if iszero(or(iszero(b), iszero(gt(a, div(not(0), b))))) {
        revert(0, 0)
      }

      c := div(mul(a, b), WAD)
    }
  }

  /// @notice Multiplies two WAD numbers, rounding up.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return c = ceil(a * b / WAD), expressed in WAD.
  function wadMulUp(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / b
      if iszero(or(iszero(b), iszero(gt(a, div(not(0), b))))) {
        revert(0, 0)
      }
      c := mul(a, b)
      // Add 1 if (a * b) % WAD > 0 to round up the division of (a * b) by WAD
      c := add(div(c, WAD), gt(mod(c, WAD), 0))
    }
  }

  /// @notice Divides two WAD numbers, rounding down.
  /// @dev Reverts if division by zero or intermediate multiplication overflows.
  /// @return c = floor(a * WAD / b), expressed in WAD.
  function wadDivDown(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / WAD
      if or(iszero(b), iszero(iszero(gt(a, div(not(0), WAD))))) {
        revert(0, 0)
      }

      c := div(mul(a, WAD), b)
    }
  }

  /// @notice Divides two WAD numbers, rounding up.
  /// @dev Reverts if division by zero or intermediate multiplication overflows.
  /// @return c = ceil(a * WAD / b), expressed in WAD.
  function wadDivUp(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / WAD
      if or(iszero(b), iszero(iszero(gt(a, div(not(0), WAD))))) {
        revert(0, 0)
      }
      c := mul(a, WAD)
      // Add 1 if (a * WAD) % b > 0 to round up the division of (a * WAD) by b
      c := add(div(c, b), gt(mod(c, b), 0))
    }
  }

  /// @notice Multiplies two RAY numbers, rounding down.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return c = floor(a * b / RAY), expressed in RAY.
  function rayMulDown(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / b
      if iszero(or(iszero(b), iszero(gt(a, div(not(0), b))))) {
        revert(0, 0)
      }

      c := div(mul(a, b), RAY)
    }
  }

  /// @notice Multiplies two RAY numbers, rounding up.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return c = ceil(a * b / RAY), expressed in RAY.
  function rayMulUp(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / b
      if iszero(or(iszero(b), iszero(gt(a, div(not(0), b))))) {
        revert(0, 0)
      }
      c := mul(a, b)
      // Add 1 if (a * b) % RAY > 0 to round up the division of (a * b) by RAY
      c := add(div(c, RAY), gt(mod(c, RAY), 0))
    }
  }

  /// @notice Divides two RAY numbers, rounding down.
  /// @dev Reverts if division by zero or intermediate multiplication overflows.
  /// @return c = floor(a * RAY / b), expressed in RAY.
  function rayDivDown(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / RAY
      if or(iszero(b), iszero(iszero(gt(a, div(not(0), RAY))))) {
        revert(0, 0)
      }

      c := div(mul(a, RAY), b)
    }
  }

  /// @notice Divides two RAY numbers, rounding up.
  /// @dev Reverts if division by zero or intermediate multiplication overflows.
  /// @return c = ceil(a * RAY / b), expressed in RAY.
  function rayDivUp(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      // to avoid overflow, a <= type(uint256).max / RAY
      if or(iszero(b), iszero(iszero(gt(a, div(not(0), RAY))))) {
        revert(0, 0)
      }
      c := mul(a, RAY)
      // Add 1 if (a * RAY) % b > 0 to round up the division of (a * RAY) by b
      c := add(div(c, b), gt(mod(c, b), 0))
    }
  }

  /// @notice Casts value to WAD, adding 18 digits of precision.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return b = a * WAD, expressed in WAD.
  function toWad(uint256 a) internal pure returns (uint256 b) {
    assembly ('memory-safe') {
      b := mul(a, WAD)

      // to avoid overflow, b/WAD == a
      if iszero(eq(div(b, WAD), a)) {
        revert(0, 0)
      }
    }
  }

  /// @notice Casts value to RAY, adding 27 digits of precision.
  /// @dev Reverts if intermediate multiplication overflows.
  /// @return b = a * RAY, expressed in RAY.
  function toRay(uint256 a) internal pure returns (uint256 b) {
    assembly ('memory-safe') {
      b := mul(a, RAY)

      // to avoid overflow, b/RAY == a
      if iszero(eq(div(b, RAY), a)) {
        revert(0, 0)
      }
    }
  }

  /// @notice Removes WAD precision from a given value, rounding down.
  /// @return b = a / WAD.
  function fromWadDown(uint256 a) internal pure returns (uint256 b) {
    assembly ('memory-safe') {
      b := div(a, WAD)
    }
  }

  /// @notice Removes RAY precision from a given value, rounding up.
  /// @return b = ceil(a / RAY).
  function fromRayUp(uint256 a) internal pure returns (uint256 b) {
    assembly ('memory-safe') {
      // add 1 if (a % RAY) > 0 to round up the division of a by RAY
      b := add(div(a, RAY), gt(mod(a, RAY), 0))
    }
  }

  /// @notice Converts value from basis points to WAD.
  /// @dev Reverts if result overflows.
  /// @return b = a * (WAD / PERCENTAGE_FACTOR), expressed in WAD.
  function bpsToWad(uint256 a) internal pure returns (uint256 b) {
    assembly ('memory-safe') {
      let factor := div(WAD, PERCENTAGE_FACTOR)
      b := mul(a, factor)
      // to avoid overflow, b/factor == a
      if iszero(eq(div(b, factor), a)) {
        revert(0, 0)
      }
    }
  }

  /// @notice Converts value from basis points to RAY.
  /// @dev Reverts if result overflows.
  /// @return b = a * (RAY / PERCENTAGE_FACTOR), expressed in RAY.
  function bpsToRay(uint256 a) internal pure returns (uint256 b) {
    assembly ('memory-safe') {
      let factor := div(RAY, PERCENTAGE_FACTOR)
      b := mul(a, factor)
      // to avoid overflow, b/factor == a
      if iszero(eq(div(b, factor), a)) {
        revert(0, 0)
      }
    }
  }

  /// @notice Rounds up a RAY value to the nearest RAY.
  /// @dev Reverts if result overflows.
  /// @return b = ceil(a / RAY) * RAY.
  function roundRayUp(uint256 a) internal pure returns (uint256 b) {
    assembly ('memory-safe') {
      // add 1 if (a % RAY) > 0 to round up the division of a by RAY
      let c := add(div(a, RAY), gt(mod(a, RAY), 0))
      b := mul(c, RAY)
      // to avoid overflow, b/RAY == c
      if iszero(eq(div(b, RAY), c)) {
        revert(0, 0)
      }
    }
  }
}

// src/spoke/interfaces/IAaveOracle.sol

/// @title IAaveOracle
/// @author Aave Labs
/// @notice Interface for the Aave Oracle.
interface IAaveOracle is IPriceOracle {
  /// @dev Emitted when the price feed source of a reserve is updated.
  /// @param reserveId The identifier of the reserve.
  /// @param source The price feed source of the reserve.
  event UpdateReserveSource(uint256 indexed reserveId, address indexed source);

  /// @dev Emitted when the Spoke is set.
  /// @param spoke The address of the Spoke.
  event SetSpoke(address indexed spoke);

  /// @dev Thrown when the caller is not the deployer.
  error OnlyDeployer();

  /// @dev Thrown when the Spoke is already set.
  error SpokeAlreadySet();

  /// @dev Thrown when the price feed source uses a different number of decimals than the oracle.
  /// @param reserveId The identifier of the reserve.
  error InvalidSourceDecimals(uint256 reserveId);

  /// @dev Thrown when the price feed source is invalid (zero address).
  /// @param reserveId The identifier of the reserve.
  error InvalidSource(uint256 reserveId);

  /// @dev Thrown when the price feed source returns an invalid price (non-positive).
  /// @param reserveId The identifier of the reserve.
  error InvalidPrice(uint256 reserveId);

  /// @dev Thrown when the given address is invalid.
  error InvalidAddress();

  /// @dev Thrown when the Spoke's oracle does not match the current oracle.
  error OracleMismatch();

  /// @notice Sets the address of the Spoke.
  /// @dev Can only be called once by the deployer.
  /// @dev The spoke should be set before any other function is called.
  /// @param spoke The address of the Spoke.
  function setSpoke(address spoke) external;

  /// @notice Sets the price feed source of a reserve.
  /// @dev Must be called by the Spoke.
  /// @dev The source must implement IPriceFeed.
  /// @param reserveId The identifier of the reserve.
  /// @param source The price feed source of the reserve.
  function setReserveSource(uint256 reserveId, address source) external;

  /// @notice Returns the prices of multiple reserves.
  /// @dev Reverts if the price of one of the reserves is not greater than 0.
  /// @param reserveIds The identifiers of the reserves.
  /// @return prices The prices of the reserves.
  function getReservesPrices(
    uint256[] calldata reserveIds
  ) external view returns (uint256[] memory);

  /// @notice Returns the price feed source of a reserve.
  /// @param reserveId The identifier of the reserve.
  /// @return source The price feed source of the reserve.
  function getReserveSource(uint256 reserveId) external view returns (address);
}

// src/interfaces/IIntentConsumer.sol

/// @title IIntentConsumer
/// @author Aave Labs
/// @notice Minimal interface for IntentConsumer.
interface IIntentConsumer is INoncesKeyed {
  /// @notice Thrown when given signature is invalid.
  error InvalidSignature();

  /// @notice Returns the EIP-712 domain separator.
  function DOMAIN_SEPARATOR() external view returns (bytes32);
}

// src/libraries/math/MathUtils.sol

/// @title MathUtils library
/// @author Aave Labs
library MathUtils {
  using SafeCast for uint256;

  uint256 internal constant RAY = 1e27;
  /// @dev Ignoring leap years
  uint256 internal constant SECONDS_PER_YEAR = 365 days;

  /// @notice Calculates the interest accumulated using a linear interest rate formula.
  /// @dev Reverts if `lastUpdateTimestamp` is greater than `block.timestamp`.
  /// @param rate The interest rate, expressed in RAY.
  /// @param lastUpdateTimestamp The timestamp to calculate interest rate from.
  /// @return result The interest rate linearly accumulated during the time delta, expressed in RAY.
  function calculateLinearInterest(
    uint96 rate,
    uint40 lastUpdateTimestamp
  ) internal view returns (uint256 result) {
    assembly ('memory-safe') {
      if gt(lastUpdateTimestamp, timestamp()) {
        revert(0, 0)
      }
      result := sub(timestamp(), lastUpdateTimestamp)
      result := add(div(mul(rate, result), SECONDS_PER_YEAR), RAY)
    }
  }

  /// @notice Returns the smaller of two unsigned integers.
  function min(uint256 a, uint256 b) internal pure returns (uint256 result) {
    assembly ('memory-safe') {
      result := xor(b, mul(xor(a, b), lt(a, b)))
    }
  }

  /// @notice Returns the saturating subtraction at zero.
  function zeroFloorSub(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      c := mul(sub(a, b), gt(a, b))
    }
  }

  /// @notice Returns the sum of an unsigned and signed integer.
  /// @dev Reverts on underflow.
  function add(uint256 a, int256 b) internal pure returns (uint256) {
    if (b >= 0) return a + uint256(b);
    return a - uint256(-b);
  }

  /// @notice Returns the sum of two unsigned integers.
  /// @dev Does not revert on overflow.
  function uncheckedAdd(uint256 a, uint256 b) internal pure returns (uint256) {
    unchecked {
      return a + b;
    }
  }

  /// @notice Returns the difference of two unsigned integers as a signed integer.
  function signedSub(uint256 a, uint256 b) internal pure returns (int256) {
    return a.toInt256() - b.toInt256();
  }

  /// @notice Returns the difference of two unsigned integers.
  /// @dev Does not revert on underflow.
  function uncheckedSub(uint256 a, uint256 b) internal pure returns (uint256) {
    unchecked {
      return a - b;
    }
  }

  /// @notice Raises an unsigned integer to the power of an unsigned integer.
  /// @dev Does not revert on overflow.
  function uncheckedExp(uint256 a, uint256 b) internal pure returns (uint256) {
    unchecked {
      return a ** b;
    }
  }

  /// @notice Divides `a` by `b`, rounding up.
  /// @dev Reverts if division by zero.
  /// @return c = ceil(a / b).
  function divUp(uint256 a, uint256 b) internal pure returns (uint256 c) {
    assembly ('memory-safe') {
      if iszero(b) {
        revert(0, 0)
      }
      c := add(div(a, b), gt(mod(a, b), 0))
    }
  }

  /// @notice Multiplies `a` and `b` in 256 bits and divides the result by `c`, rounding down.
  /// @dev Reverts if division by zero or overflow occurs on intermediate multiplication.
  /// @return d = floor(a * b / c).
  function mulDivDown(uint256 a, uint256 b, uint256 c) internal pure returns (uint256 d) {
    // to avoid overflow, a <= type(uint256).max / b
    assembly ('memory-safe') {
      if iszero(c) {
        revert(0, 0)
      }
      if iszero(or(iszero(b), iszero(gt(a, div(not(0), b))))) {
        revert(0, 0)
      }
      d := div(mul(a, b), c)
    }
  }

  /// @notice Multiplies `a` and `b` in 256 bits and divides the result by `c`, rounding up.
  /// @dev Reverts if division by zero or overflow occurs on intermediate multiplication.
  /// @return d = ceil(a * b / c).
  function mulDivUp(uint256 a, uint256 b, uint256 c) internal pure returns (uint256 d) {
    // to avoid overflow, a <= type(uint256).max / b
    assembly ('memory-safe') {
      if iszero(c) {
        revert(0, 0)
      }
      if iszero(or(iszero(b), iszero(gt(a, div(not(0), b))))) {
        revert(0, 0)
      }
      d := mul(a, b)
      // add 1 if (a * b) % c > 0 to round up the division of (a * b) by c
      d := add(div(d, c), gt(mod(d, c), 0))
    }
  }
}

// src/hub/libraries/Premium.sol

/// @title Premium library
/// @author Aave Labs
/// @notice Implements the premium calculations.
library Premium {
  using SafeCast for *;

  /// @notice Calculates the premium debt with full precision.
  /// @param premiumShares The number of premium shares.
  /// @param premiumOffsetRay The premium offset, expressed in asset units and scaled by RAY.
  /// @param drawnIndex The drawn index at which premium debt is calculated.
  /// @return The premium debt, expressed in asset units and scaled by RAY.
  function calculatePremiumRay(
    uint256 premiumShares,
    int256 premiumOffsetRay,
    uint256 drawnIndex
  ) internal pure returns (uint256) {
    return ((premiumShares * drawnIndex).toInt256() - premiumOffsetRay).toUint256();
  }
}

// src/dependencies/openzeppelin/IERC1363.sol

// OpenZeppelin Contracts (last updated v5.4.0) (interfaces/IERC1363.sol)

/**
 * @title IERC1363
 * @dev Interface of the ERC-1363 standard as defined in the https://eips.ethereum.org/EIPS/eip-1363[ERC-1363].
 *
 * Defines an extension interface for ERC-20 tokens that supports executing code on a recipient contract
 * after `transfer` or `transferFrom`, or code on a spender contract after `approve`, in a single transaction.
 */
interface IERC1363 is IERC20, IERC165 {
  /*
   * Note: the ERC-165 identifier for this interface is 0xb0202a11.
   * 0xb0202a11 ===
   *   bytes4(keccak256('transferAndCall(address,uint256)')) ^
   *   bytes4(keccak256('transferAndCall(address,uint256,bytes)')) ^
   *   bytes4(keccak256('transferFromAndCall(address,address,uint256)')) ^
   *   bytes4(keccak256('transferFromAndCall(address,address,uint256,bytes)')) ^
   *   bytes4(keccak256('approveAndCall(address,uint256)')) ^
   *   bytes4(keccak256('approveAndCall(address,uint256,bytes)'))
   */

  /**
   * @dev Moves a `value` amount of tokens from the caller's account to `to`
   * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
   * @param to The address which you want to transfer to.
   * @param value The amount of tokens to be transferred.
   * @return A boolean value indicating whether the operation succeeded unless throwing.
   */
  function transferAndCall(address to, uint256 value) external returns (bool);

  /**
   * @dev Moves a `value` amount of tokens from the caller's account to `to`
   * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
   * @param to The address which you want to transfer to.
   * @param value The amount of tokens to be transferred.
   * @param data Additional data with no specified format, sent in call to `to`.
   * @return A boolean value indicating whether the operation succeeded unless throwing.
   */
  function transferAndCall(address to, uint256 value, bytes calldata data) external returns (bool);

  /**
   * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
   * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
   * @param from The address which you want to send tokens from.
   * @param to The address which you want to transfer to.
   * @param value The amount of tokens to be transferred.
   * @return A boolean value indicating whether the operation succeeded unless throwing.
   */
  function transferFromAndCall(address from, address to, uint256 value) external returns (bool);

  /**
   * @dev Moves a `value` amount of tokens from `from` to `to` using the allowance mechanism
   * and then calls {IERC1363Receiver-onTransferReceived} on `to`.
   * @param from The address which you want to send tokens from.
   * @param to The address which you want to transfer to.
   * @param value The amount of tokens to be transferred.
   * @param data Additional data with no specified format, sent in call to `to`.
   * @return A boolean value indicating whether the operation succeeded unless throwing.
   */
  function transferFromAndCall(
    address from,
    address to,
    uint256 value,
    bytes calldata data
  ) external returns (bool);

  /**
   * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
   * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
   * @param spender The address which will spend the funds.
   * @param value The amount of tokens to be spent.
   * @return A boolean value indicating whether the operation succeeded unless throwing.
   */
  function approveAndCall(address spender, uint256 value) external returns (bool);

  /**
   * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
   * caller's tokens and then calls {IERC1363Spender-onApprovalReceived} on `spender`.
   * @param spender The address which will spend the funds.
   * @param value The amount of tokens to be spent.
   * @param data Additional data with no specified format, sent in call to `spender`.
   * @return A boolean value indicating whether the operation succeeded unless throwing.
   */
  function approveAndCall(
    address spender,
    uint256 value,
    bytes calldata data
  ) external returns (bool);
}

// src/dependencies/openzeppelin/Math.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/math/Math.sol)

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
  enum Rounding {
    Floor, // Toward negative infinity
    Ceil, // Toward positive infinity
    Trunc, // Toward zero
    Expand // Away from zero
  }

  /**
   * @dev Return the 512-bit addition of two uint256.
   *
   * The result is stored in two 256 variables such that sum = high * 2²⁵⁶ + low.
   */
  function add512(uint256 a, uint256 b) internal pure returns (uint256 high, uint256 low) {
    assembly ('memory-safe') {
      low := add(a, b)
      high := lt(low, a)
    }
  }

  /**
   * @dev Return the 512-bit multiplication of two uint256.
   *
   * The result is stored in two 256 variables such that product = high * 2²⁵⁶ + low.
   */
  function mul512(uint256 a, uint256 b) internal pure returns (uint256 high, uint256 low) {
    // 512-bit multiply [high low] = x * y. Compute the product mod 2²⁵⁶ and mod 2²⁵⁶ - 1, then use
    // the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
    // variables such that product = high * 2²⁵⁶ + low.
    assembly ('memory-safe') {
      let mm := mulmod(a, b, not(0))
      low := mul(a, b)
      high := sub(sub(mm, low), lt(mm, low))
    }
  }

  /**
   * @dev Returns the addition of two unsigned integers, with a success flag (no overflow).
   */
  function tryAdd(uint256 a, uint256 b) internal pure returns (bool success, uint256 result) {
    unchecked {
      uint256 c = a + b;
      success = c >= a;
      result = c * SafeCast.toUint(success);
    }
  }

  /**
   * @dev Returns the subtraction of two unsigned integers, with a success flag (no overflow).
   */
  function trySub(uint256 a, uint256 b) internal pure returns (bool success, uint256 result) {
    unchecked {
      uint256 c = a - b;
      success = c <= a;
      result = c * SafeCast.toUint(success);
    }
  }

  /**
   * @dev Returns the multiplication of two unsigned integers, with a success flag (no overflow).
   */
  function tryMul(uint256 a, uint256 b) internal pure returns (bool success, uint256 result) {
    unchecked {
      uint256 c = a * b;
      assembly ('memory-safe') {
        // Only true when the multiplication doesn't overflow
        // (c / a == b) || (a == 0)
        success := or(eq(div(c, a), b), iszero(a))
      }
      // equivalent to: success ? c : 0
      result = c * SafeCast.toUint(success);
    }
  }

  /**
   * @dev Returns the division of two unsigned integers, with a success flag (no division by zero).
   */
  function tryDiv(uint256 a, uint256 b) internal pure returns (bool success, uint256 result) {
    unchecked {
      success = b > 0;
      assembly ('memory-safe') {
        // The `DIV` opcode returns zero when the denominator is 0.
        result := div(a, b)
      }
    }
  }

  /**
   * @dev Returns the remainder of dividing two unsigned integers, with a success flag (no division by zero).
   */
  function tryMod(uint256 a, uint256 b) internal pure returns (bool success, uint256 result) {
    unchecked {
      success = b > 0;
      assembly ('memory-safe') {
        // The `MOD` opcode returns zero when the denominator is 0.
        result := mod(a, b)
      }
    }
  }

  /**
   * @dev Unsigned saturating addition, bounds to `2²⁵⁶ - 1` instead of overflowing.
   */
  function saturatingAdd(uint256 a, uint256 b) internal pure returns (uint256) {
    (bool success, uint256 result) = tryAdd(a, b);
    return ternary(success, result, type(uint256).max);
  }

  /**
   * @dev Unsigned saturating subtraction, bounds to zero instead of overflowing.
   */
  function saturatingSub(uint256 a, uint256 b) internal pure returns (uint256) {
    (, uint256 result) = trySub(a, b);
    return result;
  }

  /**
   * @dev Unsigned saturating multiplication, bounds to `2²⁵⁶ - 1` instead of overflowing.
   */
  function saturatingMul(uint256 a, uint256 b) internal pure returns (uint256) {
    (bool success, uint256 result) = tryMul(a, b);
    return ternary(success, result, type(uint256).max);
  }

  /**
   * @dev Branchless ternary evaluation for `condition ? a : b`. Gas costs are constant.
   *
   * IMPORTANT: This function may reduce bytecode size and consume less gas when used standalone.
   * However, the compiler may optimize Solidity ternary operations (i.e. `condition ? a : b`) to only compute
   * one branch when needed, making this function more expensive.
   */
  function ternary(bool condition, uint256 a, uint256 b) internal pure returns (uint256) {
    unchecked {
      // branchless ternary works because:
      // b ^ (a ^ b) == a
      // b ^ 0 == b
      return b ^ ((a ^ b) * SafeCast.toUint(condition));
    }
  }

  /**
   * @dev Returns the largest of two numbers.
   */
  function max(uint256 a, uint256 b) internal pure returns (uint256) {
    return ternary(a > b, a, b);
  }

  /**
   * @dev Returns the smallest of two numbers.
   */
  function min(uint256 a, uint256 b) internal pure returns (uint256) {
    return ternary(a < b, a, b);
  }

  /**
   * @dev Returns the average of two numbers. The result is rounded towards
   * zero.
   */
  function average(uint256 a, uint256 b) internal pure returns (uint256) {
    // (a + b) / 2 can overflow.
    return (a & b) + (a ^ b) / 2;
  }

  /**
   * @dev Returns the ceiling of the division of two numbers.
   *
   * This differs from standard division with `/` in that it rounds towards infinity instead
   * of rounding towards zero.
   */
  function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
    if (b == 0) {
      // Guarantee the same behavior as in a regular Solidity division.
      Panic.panic(Panic.DIVISION_BY_ZERO);
    }

    // The following calculation ensures accurate ceiling division without overflow.
    // Since a is non-zero, (a - 1) / b will not overflow.
    // The largest possible result occurs when (a - 1) / b is type(uint256).max,
    // but the largest value we can obtain is type(uint256).max - 1, which happens
    // when a = type(uint256).max and b = 1.
    unchecked {
      return SafeCast.toUint(a > 0) * ((a - 1) / b + 1);
    }
  }

  /**
   * @dev Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or
   * denominator == 0.
   *
   * Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv) with further edits by
   * Uniswap Labs also under MIT license.
   */
  function mulDiv(
    uint256 x,
    uint256 y,
    uint256 denominator
  ) internal pure returns (uint256 result) {
    unchecked {
      (uint256 high, uint256 low) = mul512(x, y);

      // Handle non-overflow cases, 256 by 256 division.
      if (high == 0) {
        // Solidity will revert if denominator == 0, unlike the div opcode on its own.
        // The surrounding unchecked block does not change this fact.
        // See https://docs.soliditylang.org/en/latest/control-structures.html#checked-or-unchecked-arithmetic.
        return low / denominator;
      }

      // Make sure the result is less than 2²⁵⁶. Also prevents denominator == 0.
      if (denominator <= high) {
        Panic.panic(ternary(denominator == 0, Panic.DIVISION_BY_ZERO, Panic.UNDER_OVERFLOW));
      }

      ///////////////////////////////////////////////
      // 512 by 256 division.
      ///////////////////////////////////////////////

      // Make division exact by subtracting the remainder from [high low].
      uint256 remainder;
      assembly ('memory-safe') {
        // Compute remainder using mulmod.
        remainder := mulmod(x, y, denominator)

        // Subtract 256 bit number from 512 bit number.
        high := sub(high, gt(remainder, low))
        low := sub(low, remainder)
      }

      // Factor powers of two out of denominator and compute largest power of two divisor of denominator.
      // Always >= 1. See https://cs.stackexchange.com/q/138556/92363.

      uint256 twos = denominator & (0 - denominator);
      assembly ('memory-safe') {
        // Divide denominator by twos.
        denominator := div(denominator, twos)

        // Divide [high low] by twos.
        low := div(low, twos)

        // Flip twos such that it is 2²⁵⁶ / twos. If twos is zero, then it becomes one.
        twos := add(div(sub(0, twos), twos), 1)
      }

      // Shift in bits from high into low.
      low |= high * twos;

      // Invert denominator mod 2²⁵⁶. Now that denominator is an odd number, it has an inverse modulo 2²⁵⁶ such
      // that denominator * inv ≡ 1 mod 2²⁵⁶. Compute the inverse by starting with a seed that is correct for
      // four bits. That is, denominator * inv ≡ 1 mod 2⁴.
      uint256 inverse = (3 * denominator) ^ 2;

      // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also
      // works in modular arithmetic, doubling the correct bits in each step.
      inverse *= 2 - denominator * inverse; // inverse mod 2⁸
      inverse *= 2 - denominator * inverse; // inverse mod 2¹⁶
      inverse *= 2 - denominator * inverse; // inverse mod 2³²
      inverse *= 2 - denominator * inverse; // inverse mod 2⁶⁴
      inverse *= 2 - denominator * inverse; // inverse mod 2¹²⁸
      inverse *= 2 - denominator * inverse; // inverse mod 2²⁵⁶

      // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
      // This will give us the correct result modulo 2²⁵⁶. Since the preconditions guarantee that the outcome is
      // less than 2²⁵⁶, this is the final result. We don't need to compute the high bits of the result and high
      // is no longer required.
      result = low * inverse;
      return result;
    }
  }

  /**
   * @dev Calculates x * y / denominator with full precision, following the selected rounding direction.
   */
  function mulDiv(
    uint256 x,
    uint256 y,
    uint256 denominator,
    Rounding rounding
  ) internal pure returns (uint256) {
    return
      mulDiv(x, y, denominator) +
      SafeCast.toUint(unsignedRoundsUp(rounding) && mulmod(x, y, denominator) > 0);
  }

  /**
   * @dev Calculates floor(x * y >> n) with full precision. Throws if result overflows a uint256.
   */
  function mulShr(uint256 x, uint256 y, uint8 n) internal pure returns (uint256 result) {
    unchecked {
      (uint256 high, uint256 low) = mul512(x, y);
      if (high >= 1 << n) {
        Panic.panic(Panic.UNDER_OVERFLOW);
      }
      return (high << (256 - n)) | (low >> n);
    }
  }

  /**
   * @dev Calculates x * y >> n with full precision, following the selected rounding direction.
   */
  function mulShr(
    uint256 x,
    uint256 y,
    uint8 n,
    Rounding rounding
  ) internal pure returns (uint256) {
    return
      mulShr(x, y, n) + SafeCast.toUint(unsignedRoundsUp(rounding) && mulmod(x, y, 1 << n) > 0);
  }

  /**
   * @dev Calculate the modular multiplicative inverse of a number in Z/nZ.
   *
   * If n is a prime, then Z/nZ is a field. In that case all elements are inversible, except 0.
   * If n is not a prime, then Z/nZ is not a field, and some elements might not be inversible.
   *
   * If the input value is not inversible, 0 is returned.
   *
   * NOTE: If you know for sure that n is (big) a prime, it may be cheaper to use Fermat's little theorem and get the
   * inverse using `Math.modExp(a, n - 2, n)`. See {invModPrime}.
   */
  function invMod(uint256 a, uint256 n) internal pure returns (uint256) {
    unchecked {
      if (n == 0) return 0;

      // The inverse modulo is calculated using the Extended Euclidean Algorithm (iterative version)
      // Used to compute integers x and y such that: ax + ny = gcd(a, n).
      // When the gcd is 1, then the inverse of a modulo n exists and it's x.
      // ax + ny = 1
      // ax = 1 + (-y)n
      // ax ≡ 1 (mod n) # x is the inverse of a modulo n

      // If the remainder is 0 the gcd is n right away.
      uint256 remainder = a % n;
      uint256 gcd = n;

      // Therefore the initial coefficients are:
      // ax + ny = gcd(a, n) = n
      // 0a + 1n = n
      int256 x = 0;
      int256 y = 1;

      while (remainder != 0) {
        uint256 quotient = gcd / remainder;

        (gcd, remainder) = (
          // The old remainder is the next gcd to try.
          remainder,
          // Compute the next remainder.
          // Can't overflow given that (a % gcd) * (gcd // (a % gcd)) <= gcd
          // where gcd is at most n (capped to type(uint256).max)
          gcd - remainder * quotient
        );

        (x, y) = (
          // Increment the coefficient of a.
          y,
          // Decrement the coefficient of n.
          // Can overflow, but the result is casted to uint256 so that the
          // next value of y is "wrapped around" to a value between 0 and n - 1.
          x - y * int256(quotient)
        );
      }

      if (gcd != 1) return 0; // No inverse exists.
      return ternary(x < 0, n - uint256(-x), uint256(x)); // Wrap the result if it's negative.
    }
  }

  /**
   * @dev Variant of {invMod}. More efficient, but only works if `p` is known to be a prime greater than `2`.
   *
   * From https://en.wikipedia.org/wiki/Fermat%27s_little_theorem[Fermat's little theorem], we know that if p is
   * prime, then `a**(p-1) ≡ 1 mod p`. As a consequence, we have `a * a**(p-2) ≡ 1 mod p`, which means that
   * `a**(p-2)` is the modular multiplicative inverse of a in Fp.
   *
   * NOTE: this function does NOT check that `p` is a prime greater than `2`.
   */
  function invModPrime(uint256 a, uint256 p) internal view returns (uint256) {
    unchecked {
      return Math.modExp(a, p - 2, p);
    }
  }

  /**
   * @dev Returns the modular exponentiation of the specified base, exponent and modulus (b ** e % m)
   *
   * Requirements:
   * - modulus can't be zero
   * - underlying staticcall to precompile must succeed
   *
   * IMPORTANT: The result is only valid if the underlying call succeeds. When using this function, make
   * sure the chain you're using it on supports the precompiled contract for modular exponentiation
   * at address 0x05 as specified in https://eips.ethereum.org/EIPS/eip-198[EIP-198]. Otherwise,
   * the underlying function will succeed given the lack of a revert, but the result may be incorrectly
   * interpreted as 0.
   */
  function modExp(uint256 b, uint256 e, uint256 m) internal view returns (uint256) {
    (bool success, uint256 result) = tryModExp(b, e, m);
    if (!success) {
      Panic.panic(Panic.DIVISION_BY_ZERO);
    }
    return result;
  }

  /**
   * @dev Returns the modular exponentiation of the specified base, exponent and modulus (b ** e % m).
   * It includes a success flag indicating if the operation succeeded. Operation will be marked as failed if trying
   * to operate modulo 0 or if the underlying precompile reverted.
   *
   * IMPORTANT: The result is only valid if the success flag is true. When using this function, make sure the chain
   * you're using it on supports the precompiled contract for modular exponentiation at address 0x05 as specified in
   * https://eips.ethereum.org/EIPS/eip-198[EIP-198]. Otherwise, the underlying function will succeed given the lack
   * of a revert, but the result may be incorrectly interpreted as 0.
   */
  function tryModExp(
    uint256 b,
    uint256 e,
    uint256 m
  ) internal view returns (bool success, uint256 result) {
    if (m == 0) return (false, 0);
    assembly ('memory-safe') {
      let ptr := mload(0x40)
      // | Offset    | Content    | Content (Hex)                                                      |
      // |-----------|------------|--------------------------------------------------------------------|
      // | 0x00:0x1f | size of b  | 0x0000000000000000000000000000000000000000000000000000000000000020 |
      // | 0x20:0x3f | size of e  | 0x0000000000000000000000000000000000000000000000000000000000000020 |
      // | 0x40:0x5f | size of m  | 0x0000000000000000000000000000000000000000000000000000000000000020 |
      // | 0x60:0x7f | value of b | 0x<.............................................................b> |
      // | 0x80:0x9f | value of e | 0x<.............................................................e> |
      // | 0xa0:0xbf | value of m | 0x<.............................................................m> |
      mstore(ptr, 0x20)
      mstore(add(ptr, 0x20), 0x20)
      mstore(add(ptr, 0x40), 0x20)
      mstore(add(ptr, 0x60), b)
      mstore(add(ptr, 0x80), e)
      mstore(add(ptr, 0xa0), m)

      // Given the result < m, it's guaranteed to fit in 32 bytes,
      // so we can use the memory scratch space located at offset 0.
      success := staticcall(gas(), 0x05, ptr, 0xc0, 0x00, 0x20)
      result := mload(0x00)
    }
  }

  /**
   * @dev Variant of {modExp} that supports inputs of arbitrary length.
   */
  function modExp(
    bytes memory b,
    bytes memory e,
    bytes memory m
  ) internal view returns (bytes memory) {
    (bool success, bytes memory result) = tryModExp(b, e, m);
    if (!success) {
      Panic.panic(Panic.DIVISION_BY_ZERO);
    }
    return result;
  }

  /**
   * @dev Variant of {tryModExp} that supports inputs of arbitrary length.
   */
  function tryModExp(
    bytes memory b,
    bytes memory e,
    bytes memory m
  ) internal view returns (bool success, bytes memory result) {
    if (_zeroBytes(m)) return (false, new bytes(0));

    uint256 mLen = m.length;

    // Encode call args in result and move the free memory pointer
    result = abi.encodePacked(b.length, e.length, mLen, b, e, m);

    assembly ('memory-safe') {
      let dataPtr := add(result, 0x20)
      // Write result on top of args to avoid allocating extra memory.
      success := staticcall(gas(), 0x05, dataPtr, mload(result), dataPtr, mLen)
      // Overwrite the length.
      // result.length > returndatasize() is guaranteed because returndatasize() == m.length
      mstore(result, mLen)
      // Set the memory pointer after the returned data.
      mstore(0x40, add(dataPtr, mLen))
    }
  }

  /**
   * @dev Returns whether the provided byte array is zero.
   */
  function _zeroBytes(bytes memory byteArray) private pure returns (bool) {
    for (uint256 i = 0; i < byteArray.length; ++i) {
      if (byteArray[i] != 0) {
        return false;
      }
    }
    return true;
  }

  /**
   * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded
   * towards zero.
   *
   * This method is based on Newton's method for computing square roots; the algorithm is restricted to only
   * using integer operations.
   */
  function sqrt(uint256 a) internal pure returns (uint256) {
    unchecked {
      // Take care of easy edge cases when a == 0 or a == 1
      if (a <= 1) {
        return a;
      }

      // In this function, we use Newton's method to get a root of `f(x) := x² - a`. It involves building a
      // sequence x_n that converges toward sqrt(a). For each iteration x_n, we also define the error between
      // the current value as `ε_n = | x_n - sqrt(a) |`.
      //
      // For our first estimation, we consider `e` the smallest power of 2 which is bigger than the square root
      // of the target. (i.e. `2**(e-1) ≤ sqrt(a) < 2**e`). We know that `e ≤ 128` because `(2¹²⁸)² = 2²⁵⁶` is
      // bigger than any uint256.
      //
      // By noticing that
      // `2**(e-1) ≤ sqrt(a) < 2**e → (2**(e-1))² ≤ a < (2**e)² → 2**(2*e-2) ≤ a < 2**(2*e)`
      // we can deduce that `e - 1` is `log2(a) / 2`. We can thus compute `x_n = 2**(e-1)` using a method similar
      // to the msb function.
      uint256 aa = a;
      uint256 xn = 1;

      if (aa >= (1 << 128)) {
        aa >>= 128;
        xn <<= 64;
      }
      if (aa >= (1 << 64)) {
        aa >>= 64;
        xn <<= 32;
      }
      if (aa >= (1 << 32)) {
        aa >>= 32;
        xn <<= 16;
      }
      if (aa >= (1 << 16)) {
        aa >>= 16;
        xn <<= 8;
      }
      if (aa >= (1 << 8)) {
        aa >>= 8;
        xn <<= 4;
      }
      if (aa >= (1 << 4)) {
        aa >>= 4;
        xn <<= 2;
      }
      if (aa >= (1 << 2)) {
        xn <<= 1;
      }

      // We now have x_n such that `x_n = 2**(e-1) ≤ sqrt(a) < 2**e = 2 * x_n`. This implies ε_n ≤ 2**(e-1).
      //
      // We can refine our estimation by noticing that the middle of that interval minimizes the error.
      // If we move x_n to equal 2**(e-1) + 2**(e-2), then we reduce the error to ε_n ≤ 2**(e-2).
      // This is going to be our x_0 (and ε_0)
      xn = (3 * xn) >> 1; // ε_0 := | x_0 - sqrt(a) | ≤ 2**(e-2)

      // From here, Newton's method give us:
      // x_{n+1} = (x_n + a / x_n) / 2
      //
      // One should note that:
      // x_{n+1}² - a = ((x_n + a / x_n) / 2)² - a
      //              = ((x_n² + a) / (2 * x_n))² - a
      //              = (x_n⁴ + 2 * a * x_n² + a²) / (4 * x_n²) - a
      //              = (x_n⁴ + 2 * a * x_n² + a² - 4 * a * x_n²) / (4 * x_n²)
      //              = (x_n⁴ - 2 * a * x_n² + a²) / (4 * x_n²)
      //              = (x_n² - a)² / (2 * x_n)²
      //              = ((x_n² - a) / (2 * x_n))²
      //              ≥ 0
      // Which proves that for all n ≥ 1, sqrt(a) ≤ x_n
      //
      // This gives us the proof of quadratic convergence of the sequence:
      // ε_{n+1} = | x_{n+1} - sqrt(a) |
      //         = | (x_n + a / x_n) / 2 - sqrt(a) |
      //         = | (x_n² + a - 2*x_n*sqrt(a)) / (2 * x_n) |
      //         = | (x_n - sqrt(a))² / (2 * x_n) |
      //         = | ε_n² / (2 * x_n) |
      //         = ε_n² / | (2 * x_n) |
      //
      // For the first iteration, we have a special case where x_0 is known:
      // ε_1 = ε_0² / | (2 * x_0) |
      //     ≤ (2**(e-2))² / (2 * (2**(e-1) + 2**(e-2)))
      //     ≤ 2**(2*e-4) / (3 * 2**(e-1))
      //     ≤ 2**(e-3) / 3
      //     ≤ 2**(e-3-log2(3))
      //     ≤ 2**(e-4.5)
      //
      // For the following iterations, we use the fact that, 2**(e-1) ≤ sqrt(a) ≤ x_n:
      // ε_{n+1} = ε_n² / | (2 * x_n) |
      //         ≤ (2**(e-k))² / (2 * 2**(e-1))
      //         ≤ 2**(2*e-2*k) / 2**e
      //         ≤ 2**(e-2*k)
      xn = (xn + a / xn) >> 1; // ε_1 := | x_1 - sqrt(a) | ≤ 2**(e-4.5)  -- special case, see above
      xn = (xn + a / xn) >> 1; // ε_2 := | x_2 - sqrt(a) | ≤ 2**(e-9)    -- general case with k = 4.5
      xn = (xn + a / xn) >> 1; // ε_3 := | x_3 - sqrt(a) | ≤ 2**(e-18)   -- general case with k = 9
      xn = (xn + a / xn) >> 1; // ε_4 := | x_4 - sqrt(a) | ≤ 2**(e-36)   -- general case with k = 18
      xn = (xn + a / xn) >> 1; // ε_5 := | x_5 - sqrt(a) | ≤ 2**(e-72)   -- general case with k = 36
      xn = (xn + a / xn) >> 1; // ε_6 := | x_6 - sqrt(a) | ≤ 2**(e-144)  -- general case with k = 72

      // Because e ≤ 128 (as discussed during the first estimation phase), we know have reached a precision
      // ε_6 ≤ 2**(e-144) < 1. Given we're operating on integers, then we can ensure that xn is now either
      // sqrt(a) or sqrt(a) + 1.
      return xn - SafeCast.toUint(xn > a / xn);
    }
  }

  /**
   * @dev Calculates sqrt(a), following the selected rounding direction.
   */
  function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
    unchecked {
      uint256 result = sqrt(a);
      return result + SafeCast.toUint(unsignedRoundsUp(rounding) && result * result < a);
    }
  }

  /**
   * @dev Return the log in base 2 of a positive value rounded towards zero.
   * Returns 0 if given 0.
   */
  function log2(uint256 x) internal pure returns (uint256 r) {
    // If value has upper 128 bits set, log2 result is at least 128
    r = SafeCast.toUint(x > 0xffffffffffffffffffffffffffffffff) << 7;
    // If upper 64 bits of 128-bit half set, add 64 to result
    r |= SafeCast.toUint((x >> r) > 0xffffffffffffffff) << 6;
    // If upper 32 bits of 64-bit half set, add 32 to result
    r |= SafeCast.toUint((x >> r) > 0xffffffff) << 5;
    // If upper 16 bits of 32-bit half set, add 16 to result
    r |= SafeCast.toUint((x >> r) > 0xffff) << 4;
    // If upper 8 bits of 16-bit half set, add 8 to result
    r |= SafeCast.toUint((x >> r) > 0xff) << 3;
    // If upper 4 bits of 8-bit half set, add 4 to result
    r |= SafeCast.toUint((x >> r) > 0xf) << 2;

    // Shifts value right by the current result and use it as an index into this lookup table:
    //
    // | x (4 bits) |  index  | table[index] = MSB position |
    // |------------|---------|-----------------------------|
    // |    0000    |    0    |        table[0] = 0         |
    // |    0001    |    1    |        table[1] = 0         |
    // |    0010    |    2    |        table[2] = 1         |
    // |    0011    |    3    |        table[3] = 1         |
    // |    0100    |    4    |        table[4] = 2         |
    // |    0101    |    5    |        table[5] = 2         |
    // |    0110    |    6    |        table[6] = 2         |
    // |    0111    |    7    |        table[7] = 2         |
    // |    1000    |    8    |        table[8] = 3         |
    // |    1001    |    9    |        table[9] = 3         |
    // |    1010    |   10    |        table[10] = 3        |
    // |    1011    |   11    |        table[11] = 3        |
    // |    1100    |   12    |        table[12] = 3        |
    // |    1101    |   13    |        table[13] = 3        |
    // |    1110    |   14    |        table[14] = 3        |
    // |    1111    |   15    |        table[15] = 3        |
    //
    // The lookup table is represented as a 32-byte value with the MSB positions for 0-15 in the last 16 bytes.
    assembly ('memory-safe') {
      r := or(
        r,
        byte(shr(r, x), 0x0000010102020202030303030303030300000000000000000000000000000000)
      )
    }
  }

  /**
   * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
   * Returns 0 if given 0.
   */
  function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
    unchecked {
      uint256 result = log2(value);
      return result + SafeCast.toUint(unsignedRoundsUp(rounding) && 1 << result < value);
    }
  }

  /**
   * @dev Return the log in base 10 of a positive value rounded towards zero.
   * Returns 0 if given 0.
   */
  function log10(uint256 value) internal pure returns (uint256) {
    uint256 result = 0;
    unchecked {
      if (value >= 10 ** 64) {
        value /= 10 ** 64;
        result += 64;
      }
      if (value >= 10 ** 32) {
        value /= 10 ** 32;
        result += 32;
      }
      if (value >= 10 ** 16) {
        value /= 10 ** 16;
        result += 16;
      }
      if (value >= 10 ** 8) {
        value /= 10 ** 8;
        result += 8;
      }
      if (value >= 10 ** 4) {
        value /= 10 ** 4;
        result += 4;
      }
      if (value >= 10 ** 2) {
        value /= 10 ** 2;
        result += 2;
      }
      if (value >= 10 ** 1) {
        result += 1;
      }
    }
    return result;
  }

  /**
   * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
   * Returns 0 if given 0.
   */
  function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
    unchecked {
      uint256 result = log10(value);
      return result + SafeCast.toUint(unsignedRoundsUp(rounding) && 10 ** result < value);
    }
  }

  /**
   * @dev Return the log in base 256 of a positive value rounded towards zero.
   * Returns 0 if given 0.
   *
   * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
   */
  function log256(uint256 x) internal pure returns (uint256 r) {
    // If value has upper 128 bits set, log2 result is at least 128
    r = SafeCast.toUint(x > 0xffffffffffffffffffffffffffffffff) << 7;
    // If upper 64 bits of 128-bit half set, add 64 to result
    r |= SafeCast.toUint((x >> r) > 0xffffffffffffffff) << 6;
    // If upper 32 bits of 64-bit half set, add 32 to result
    r |= SafeCast.toUint((x >> r) > 0xffffffff) << 5;
    // If upper 16 bits of 32-bit half set, add 16 to result
    r |= SafeCast.toUint((x >> r) > 0xffff) << 4;
    // Add 1 if upper 8 bits of 16-bit half set, and divide accumulated result by 8
    return (r >> 3) | SafeCast.toUint((x >> r) > 0xff);
  }

  /**
   * @dev Return the log in base 256, following the selected rounding direction, of a positive value.
   * Returns 0 if given 0.
   */
  function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
    unchecked {
      uint256 result = log256(value);
      return result + SafeCast.toUint(unsignedRoundsUp(rounding) && 1 << (result << 3) < value);
    }
  }

  /**
   * @dev Returns whether a provided rounding mode is considered rounding up for unsigned integers.
   */
  function unsignedRoundsUp(Rounding rounding) internal pure returns (bool) {
    return uint8(rounding) % 2 == 1;
  }

  /**
   * @dev Counts the number of leading zero bits in a uint256.
   */
  function clz(uint256 x) internal pure returns (uint256) {
    return ternary(x == 0, 256, 255 - log2(x));
  }
}

// src/dependencies/openzeppelin/SafeERC20.sol

// OpenZeppelin Contracts (last updated v5.5.0) (token/ERC20/utils/SafeERC20.sol)

/**
 * @title SafeERC20
 * @dev Wrappers around ERC-20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
  /**
   * @dev An operation with an ERC-20 token failed.
   */
  error SafeERC20FailedOperation(address token);

  /**
   * @dev Indicates a failed `decreaseAllowance` request.
   */
  error SafeERC20FailedDecreaseAllowance(
    address spender,
    uint256 currentAllowance,
    uint256 requestedDecrease
  );

  /**
   * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
   * non-reverting calls are assumed to be successful.
   */
  function safeTransfer(IERC20 token, address to, uint256 value) internal {
    if (!_safeTransfer(token, to, value, true)) {
      revert SafeERC20FailedOperation(address(token));
    }
  }

  /**
   * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
   * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
   */
  function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
    if (!_safeTransferFrom(token, from, to, value, true)) {
      revert SafeERC20FailedOperation(address(token));
    }
  }

  /**
   * @dev Variant of {safeTransfer} that returns a bool instead of reverting if the operation is not successful.
   */
  function trySafeTransfer(IERC20 token, address to, uint256 value) internal returns (bool) {
    return _safeTransfer(token, to, value, false);
  }

  /**
   * @dev Variant of {safeTransferFrom} that returns a bool instead of reverting if the operation is not successful.
   */
  function trySafeTransferFrom(
    IERC20 token,
    address from,
    address to,
    uint256 value
  ) internal returns (bool) {
    return _safeTransferFrom(token, from, to, value, false);
  }

  /**
   * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
   * non-reverting calls are assumed to be successful.
   *
   * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
   * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
   * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
   * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
   */
  function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
    uint256 oldAllowance = token.allowance(address(this), spender);
    forceApprove(token, spender, oldAllowance + value);
  }

  /**
   * @dev Decrease the calling contract's allowance toward `spender` by `requestedDecrease`. If `token` returns no
   * value, non-reverting calls are assumed to be successful.
   *
   * IMPORTANT: If the token implements ERC-7674 (ERC-20 with temporary allowance), and if the "client"
   * smart contract uses ERC-7674 to set temporary allowances, then the "client" smart contract should avoid using
   * this function. Performing a {safeIncreaseAllowance} or {safeDecreaseAllowance} operation on a token contract
   * that has a non-zero temporary allowance (for that particular owner-spender) will result in unexpected behavior.
   */
  function safeDecreaseAllowance(
    IERC20 token,
    address spender,
    uint256 requestedDecrease
  ) internal {
    unchecked {
      uint256 currentAllowance = token.allowance(address(this), spender);
      if (currentAllowance < requestedDecrease) {
        revert SafeERC20FailedDecreaseAllowance(spender, currentAllowance, requestedDecrease);
      }
      forceApprove(token, spender, currentAllowance - requestedDecrease);
    }
  }

  /**
   * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
   * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
   * to be set to zero before setting it to a non-zero value, such as USDT.
   *
   * NOTE: If the token implements ERC-7674, this function will not modify any temporary allowance. This function
   * only sets the "standard" allowance. Any temporary allowance will remain active, in addition to the value being
   * set here.
   */
  function forceApprove(IERC20 token, address spender, uint256 value) internal {
    if (!_safeApprove(token, spender, value, false)) {
      if (!_safeApprove(token, spender, 0, true)) revert SafeERC20FailedOperation(address(token));
      if (!_safeApprove(token, spender, value, true))
        revert SafeERC20FailedOperation(address(token));
    }
  }

  /**
   * @dev Performs an {ERC1363} transferAndCall, with a fallback to the simple {ERC20} transfer if the target has no
   * code. This can be used to implement an {ERC721}-like safe transfer that relies on {ERC1363} checks when
   * targeting contracts.
   *
   * Reverts if the returned value is other than `true`.
   */
  function transferAndCallRelaxed(
    IERC1363 token,
    address to,
    uint256 value,
    bytes memory data
  ) internal {
    if (to.code.length == 0) {
      safeTransfer(token, to, value);
    } else if (!token.transferAndCall(to, value, data)) {
      revert SafeERC20FailedOperation(address(token));
    }
  }

  /**
   * @dev Performs an {ERC1363} transferFromAndCall, with a fallback to the simple {ERC20} transferFrom if the target
   * has no code. This can be used to implement an {ERC721}-like safe transfer that relies on {ERC1363} checks when
   * targeting contracts.
   *
   * Reverts if the returned value is other than `true`.
   */
  function transferFromAndCallRelaxed(
    IERC1363 token,
    address from,
    address to,
    uint256 value,
    bytes memory data
  ) internal {
    if (to.code.length == 0) {
      safeTransferFrom(token, from, to, value);
    } else if (!token.transferFromAndCall(from, to, value, data)) {
      revert SafeERC20FailedOperation(address(token));
    }
  }

  /**
   * @dev Performs an {ERC1363} approveAndCall, with a fallback to the simple {ERC20} approve if the target has no
   * code. This can be used to implement an {ERC721}-like safe transfer that rely on {ERC1363} checks when
   * targeting contracts.
   *
   * NOTE: When the recipient address (`to`) has no code (i.e. is an EOA), this function behaves as {forceApprove}.
   * Oppositely, when the recipient address (`to`) has code, this function only attempts to call {ERC1363-approveAndCall}
   * once without retrying, and relies on the returned value to be true.
   *
   * Reverts if the returned value is other than `true`.
   */
  function approveAndCallRelaxed(
    IERC1363 token,
    address to,
    uint256 value,
    bytes memory data
  ) internal {
    if (to.code.length == 0) {
      forceApprove(token, to, value);
    } else if (!token.approveAndCall(to, value, data)) {
      revert SafeERC20FailedOperation(address(token));
    }
  }

  /**
   * @dev Imitates a Solidity `token.transfer(to, value)` call, relaxing the requirement on the return value: the
   * return value is optional (but if data is returned, it must not be false).
   *
   * @param token The token targeted by the call.
   * @param to The recipient of the tokens
   * @param value The amount of token to transfer
   * @param bubble Behavior switch if the transfer call reverts: bubble the revert reason or return a false boolean.
   */
  function _safeTransfer(
    IERC20 token,
    address to,
    uint256 value,
    bool bubble
  ) private returns (bool success) {
    bytes4 selector = IERC20.transfer.selector;

    assembly ('memory-safe') {
      let fmp := mload(0x40)
      mstore(0x00, selector)
      mstore(0x04, and(to, shr(96, not(0))))
      mstore(0x24, value)
      success := call(gas(), token, 0, 0x00, 0x44, 0x00, 0x20)
      // if call success and return is true, all is good.
      // otherwise (not success or return is not true), we need to perform further checks
      if iszero(and(success, eq(mload(0x00), 1))) {
        // if the call was a failure and bubble is enabled, bubble the error
        if and(iszero(success), bubble) {
          returndatacopy(fmp, 0x00, returndatasize())
          revert(fmp, returndatasize())
        }
        // if the return value is not true, then the call is only successful if:
        // - the token address has code
        // - the returndata is empty
        success := and(success, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
      }
      mstore(0x40, fmp)
    }
  }

  /**
   * @dev Imitates a Solidity `token.transferFrom(from, to, value)` call, relaxing the requirement on the return
   * value: the return value is optional (but if data is returned, it must not be false).
   *
   * @param token The token targeted by the call.
   * @param from The sender of the tokens
   * @param to The recipient of the tokens
   * @param value The amount of token to transfer
   * @param bubble Behavior switch if the transfer call reverts: bubble the revert reason or return a false boolean.
   */
  function _safeTransferFrom(
    IERC20 token,
    address from,
    address to,
    uint256 value,
    bool bubble
  ) private returns (bool success) {
    bytes4 selector = IERC20.transferFrom.selector;

    assembly ('memory-safe') {
      let fmp := mload(0x40)
      mstore(0x00, selector)
      mstore(0x04, and(from, shr(96, not(0))))
      mstore(0x24, and(to, shr(96, not(0))))
      mstore(0x44, value)
      success := call(gas(), token, 0, 0x00, 0x64, 0x00, 0x20)
      // if call success and return is true, all is good.
      // otherwise (not success or return is not true), we need to perform further checks
      if iszero(and(success, eq(mload(0x00), 1))) {
        // if the call was a failure and bubble is enabled, bubble the error
        if and(iszero(success), bubble) {
          returndatacopy(fmp, 0x00, returndatasize())
          revert(fmp, returndatasize())
        }
        // if the return value is not true, then the call is only successful if:
        // - the token address has code
        // - the returndata is empty
        success := and(success, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
      }
      mstore(0x40, fmp)
      mstore(0x60, 0)
    }
  }

  /**
   * @dev Imitates a Solidity `token.approve(spender, value)` call, relaxing the requirement on the return value:
   * the return value is optional (but if data is returned, it must not be false).
   *
   * @param token The token targeted by the call.
   * @param spender The spender of the tokens
   * @param value The amount of token to transfer
   * @param bubble Behavior switch if the transfer call reverts: bubble the revert reason or return a false boolean.
   */
  function _safeApprove(
    IERC20 token,
    address spender,
    uint256 value,
    bool bubble
  ) private returns (bool success) {
    bytes4 selector = IERC20.approve.selector;

    assembly ('memory-safe') {
      let fmp := mload(0x40)
      mstore(0x00, selector)
      mstore(0x04, and(spender, shr(96, not(0))))
      mstore(0x24, value)
      success := call(gas(), token, 0, 0x00, 0x44, 0x00, 0x20)
      // if call success and return is true, all is good.
      // otherwise (not success or return is not true), we need to perform further checks
      if iszero(and(success, eq(mload(0x00), 1))) {
        // if the call was a failure and bubble is enabled, bubble the error
        if and(iszero(success), bubble) {
          returndatacopy(fmp, 0x00, returndatasize())
          revert(fmp, returndatasize())
        }
        // if the return value is not true, then the call is only successful if:
        // - the token address has code
        // - the returndata is empty
        success := and(success, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
      }
      mstore(0x40, fmp)
    }
  }
}

// src/spoke/interfaces/ISpoke.sol

type ReserveFlags is uint8;

/// @title ISpoke
/// @author Aave Labs
/// @notice Full interface for Spoke.
interface ISpoke is IAccessManaged, IIntentConsumer, IExtSload, IMulticall {
  /// @notice Intent data to set user position managers with EIP712-typed signature.
  /// @param onBehalfOf The address of the user on whose behalf position manager can act.
  /// @param updates The array of position manager updates.
  /// @param nonce The nonce for the signature.
  /// @param deadline The deadline for the signature.
  struct SetUserPositionManagers {
    address onBehalfOf;
    PositionManagerUpdate[] updates;
    uint256 nonce;
    uint256 deadline;
  }

  /// @notice Sub-Intent data to apply position manager update for user.
  /// @param positionManager The address of the position manager.
  /// @param approve True to approve the position manager, false to revoke approval.
  struct PositionManagerUpdate {
    address positionManager;
    bool approve;
  }

  /// @notice Reserve level data.
  /// @dev underlying The address of the underlying asset.
  /// @dev hub The address of the associated Hub.
  /// @dev assetId The identifier of the asset in the Hub.
  /// @dev decimals The number of decimals of the underlying asset.
  /// @dev collateralRisk The risk associated with a collateral asset, expressed in BPS.
  /// @dev flags The packed boolean flags of the reserve (a wrapped uint8).
  /// @dev dynamicConfigKey The key of the last reserve dynamic config.
  struct Reserve {
    address underlying;
    //
    IHubBase hub;
    uint16 assetId;
    uint8 decimals;
    uint24 collateralRisk;
    ReserveFlags flags;
    uint32 dynamicConfigKey;
  }

  /// @notice Reserve configuration. Subset of the `Reserve` struct.
  /// @dev collateralRisk The risk associated with a collateral asset, expressed in BPS.
  /// @dev paused True if all actions are prevented for the reserve.
  /// @dev frozen True if new activity is prevented for the reserve.
  /// @dev borrowable True if the reserve is borrowable.
  /// @dev receiveSharesEnabled True if the liquidator can receive collateral shares during liquidation.
  struct ReserveConfig {
    uint24 collateralRisk;
    bool paused;
    bool frozen;
    bool borrowable;
    bool receiveSharesEnabled;
  }

  /// @notice Dynamic reserve configuration data.
  /// @dev collateralFactor The proportion of a reserve's value eligible to be used as collateral, expressed in BPS.
  /// @dev maxLiquidationBonus The maximum extra amount of collateral given to the liquidator as bonus, expressed in BPS. 100_00 represents 0.00% bonus.
  /// @dev liquidationFee The protocol fee charged on liquidations, taken from the collateral bonus given to the liquidator, expressed in BPS.
  struct DynamicReserveConfig {
    uint16 collateralFactor;
    uint32 maxLiquidationBonus;
    uint16 liquidationFee;
  }

  /// @notice Liquidation configuration data.
  /// @dev targetHealthFactor The ideal health factor to restore a user position during liquidation, expressed in WAD.
  /// @dev healthFactorForMaxBonus The health factor under which liquidation bonus is maximum, expressed in WAD.
  /// @dev liquidationBonusFactor The value multiplied by `maxLiquidationBonus` to compute the minimum liquidation bonus, expressed in BPS.
  struct LiquidationConfig {
    uint128 targetHealthFactor;
    uint64 healthFactorForMaxBonus;
    uint16 liquidationBonusFactor;
  }

  /// @notice User position data per reserve.
  /// @dev drawnShares The drawn shares of the user position.
  /// @dev premiumShares The premium shares of the user position.
  /// @dev premiumOffsetRay The premium offset of the user position, used to calculate the premium, expressed in asset units and scaled by RAY.
  /// @dev suppliedShares The supplied shares of the user position.
  /// @dev dynamicConfigKey The key of the user position dynamic config.
  struct UserPosition {
    uint120 drawnShares;
    uint120 premiumShares;
    //
    int200 premiumOffsetRay;
    //
    uint120 suppliedShares;
    uint32 dynamicConfigKey;
  }

  /// @notice Position manager configuration data.
  /// @dev approval The mapping of position manager user approvals.
  /// @dev active True if the position manager is active.
  struct PositionManagerConfig {
    mapping(address user => bool) approval;
    bool active;
  }

  /// @notice User position status data.
  /// @dev map The map of bitmap buckets for the position status.
  /// @dev riskPremium The risk premium of the user position, expressed in BPS.
  struct PositionStatus {
    mapping(uint256 bucket => uint256) map;
    uint24 riskPremium;
  }

  /// @notice User account data describing a user position and its health.
  /// @dev riskPremium The risk premium of the user position, expressed in BPS.
  /// @dev avgCollateralFactor The weighted average collateral factor of the user position, expressed in WAD.
  /// @dev healthFactor The health factor of the user position, expressed in WAD. 1e18 represents a health factor of 1.00.
  /// @dev totalCollateralValue The total collateral value of the user position, expressed in units of Value.
  /// @dev totalDebtValueRay The total debt value of the user position, expressed in units of Value and scaled by RAY.
  /// @dev activeCollateralCount The number of active collaterals, which includes reserves with `collateralFactor` > 0, `enabledAsCollateral` and `suppliedAmount` > 0.
  /// @dev borrowCount The number of borrowed reserves of the user position.
  struct UserAccountData {
    uint256 riskPremium;
    uint256 avgCollateralFactor;
    uint256 healthFactor;
    uint256 totalCollateralValue;
    uint256 totalDebtValueRay;
    uint256 activeCollateralCount;
    uint256 borrowCount;
  }

  /// @notice Emitted when the immutable variables of the Spoke are set.
  /// @param oracle The address of the oracle.
  /// @param maxUserReservesLimit The max user reserves limit.
  event SetSpokeImmutables(address indexed oracle, uint16 maxUserReservesLimit);

  /// @notice Emitted when a liquidation config is updated.
  /// @param config The new liquidation config.
  event UpdateLiquidationConfig(LiquidationConfig config);

  /// @notice Emitted when a reserve is added.
  /// @param reserveId The identifier of the reserve.
  /// @param assetId The identifier of the asset.
  /// @param hub The address of the Hub where the asset is listed.
  event AddReserve(uint256 indexed reserveId, uint256 indexed assetId, address indexed hub);

  /// @notice Emitted when a reserve configuration is updated.
  /// @param reserveId The identifier of the reserve.
  /// @param config The reserve configuration.
  event UpdateReserveConfig(uint256 indexed reserveId, ReserveConfig config);

  /// @notice Emitted when the price source of a reserve is updated.
  /// @param reserveId The identifier of the reserve.
  /// @param priceSource The address of the new price source.
  event UpdateReservePriceSource(uint256 indexed reserveId, address indexed priceSource);

  /// @notice Emitted when a dynamic reserve config is added.
  /// @dev The config key is the next available key for the reserve, which is now the latest config
  /// key of the reserve.
  /// @param reserveId The identifier of the reserve.
  /// @param dynamicConfigKey The key of the added dynamic config.
  /// @param config The dynamic reserve config.
  event AddDynamicReserveConfig(
    uint256 indexed reserveId,
    uint32 indexed dynamicConfigKey,
    DynamicReserveConfig config
  );

  /// @notice Emitted when a dynamic reserve config is updated.
  /// @param reserveId The identifier of the reserve.
  /// @param dynamicConfigKey The key of the updated dynamic config.
  /// @param config The dynamic reserve config.
  event UpdateDynamicReserveConfig(
    uint256 indexed reserveId,
    uint32 indexed dynamicConfigKey,
    DynamicReserveConfig config
  );

  /// @notice Emitted on updatePositionManager action.
  /// @param positionManager The address of the position manager.
  /// @param active True if position manager has become active.
  event UpdatePositionManager(address indexed positionManager, bool active);

  /// @notice Emitted on the supply action.
  /// @param reserveId The reserve identifier of the underlying asset.
  /// @param caller The transaction initiator, and supplier of the underlying asset.
  /// @param user The owner of the modified position.
  /// @param suppliedShares The amount of supply shares minted.
  /// @param suppliedAmount The amount of underlying asset supplied.
  event Supply(
    uint256 indexed reserveId,
    address indexed caller,
    address indexed user,
    uint256 suppliedShares,
    uint256 suppliedAmount
  );

  /// @notice Emitted on the withdraw action.
  /// @param reserveId The reserve identifier of the underlying asset.
  /// @param caller The transaction initiator, and recipient of the underlying asset being withdrawn.
  /// @param user The owner of the modified position.
  /// @param withdrawnShares The amount of supply shares burned.
  /// @param withdrawnAmount The amount of underlying asset withdrawn.
  event Withdraw(
    uint256 indexed reserveId,
    address indexed caller,
    address indexed user,
    uint256 withdrawnShares,
    uint256 withdrawnAmount
  );

  /// @notice Emitted on the borrow action.
  /// @param reserveId The reserve identifier of the underlying asset.
  /// @param caller The transaction initiator, and recipient of the underlying asset being borrowed.
  /// @param user The owner of the position on which debt is generated.
  /// @param drawnShares The amount of debt shares minted.
  /// @param drawnAmount The amount of underlying asset borrowed.
  event Borrow(
    uint256 indexed reserveId,
    address indexed caller,
    address indexed user,
    uint256 drawnShares,
    uint256 drawnAmount
  );

  /// @notice Emitted on the repay action.
  /// @param reserveId The reserve identifier of the underlying asset.
  /// @param caller The transaction initiator who is repaying the underlying asset.
  /// @param user The owner of the position whose debt is being repaid.
  /// @param drawnShares The amount of drawn shares burned.
  /// @param totalAmountRepaid The amount of drawn and premium underlying assets repaid.
  /// @param premiumDelta A struct representing the changes to premium debt after repayment.
  event Repay(
    uint256 indexed reserveId,
    address indexed caller,
    address indexed user,
    uint256 drawnShares,
    uint256 totalAmountRepaid,
    IHubBase.PremiumDelta premiumDelta
  );

  /// @dev Emitted when a borrower is liquidated.
  /// @param collateralReserveId The identifier of the reserve used as collateral, to receive as a result of the liquidation.
  /// @param debtReserveId The identifier of the reserve to be repaid with the liquidation.
  /// @param user The address of the borrower getting liquidated.
  /// @param liquidator The address of the liquidator.
  /// @param receiveShares True if the liquidator received collateral in supplied shares rather than underlying assets.
  /// @param debtAmountRestored The amount of debt restored, expressed in asset units.
  /// @param drawnSharesLiquidated The amount of drawn shares liquidated.
  /// @param premiumDelta A struct representing the changes to premium debt after liquidation.
  /// @param collateralAmountRemoved The amount of collateral removed, expressed in asset units.
  /// @param collateralSharesLiquidated The total amount of collateral shares liquidated.
  /// @param collateralSharesToLiquidator The amount of collateral shares that the liquidator received.
  event LiquidationCall(
    uint256 indexed collateralReserveId,
    uint256 indexed debtReserveId,
    address indexed user,
    address liquidator,
    bool receiveShares,
    uint256 debtAmountRestored,
    uint256 drawnSharesLiquidated,
    IHubBase.PremiumDelta premiumDelta,
    uint256 collateralAmountRemoved,
    uint256 collateralSharesLiquidated,
    uint256 collateralSharesToLiquidator
  );

  /// @notice Emitted when a reserve deficit is reported to the Hub.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @param drawnShares The amount of drawn shares reported as deficit.
  /// @param premiumDelta The premium delta data struct reported as deficit.
  event ReportDeficit(
    uint256 indexed reserveId,
    address indexed user,
    uint256 drawnShares,
    IHubBase.PremiumDelta premiumDelta
  );

  /// @notice Emitted on setUsingAsCollateral action.
  /// @param reserveId The reserve identifier of the underlying asset.
  /// @param caller The transaction initiator.
  /// @param user The owner of the position being modified.
  /// @param usingAsCollateral Whether the reserve is enabled or disabled as collateral.
  event SetUsingAsCollateral(
    uint256 indexed reserveId,
    address indexed caller,
    address indexed user,
    bool usingAsCollateral
  );

  /// @notice Emitted on updateUserRiskPremium action.
  /// @param user The owner of the position being modified.
  /// @param riskPremium The new risk premium (BPS) value of user.
  event UpdateUserRiskPremium(address indexed user, uint256 riskPremium);

  /// @notice Emitted when a user's dynamic config is refreshed for all reserves to their latest config key.
  /// @param user The address of the user.
  event RefreshAllUserDynamicConfig(address indexed user);

  /// @notice Emitted when a user's dynamic config is refreshed for a single reserve to its latest config key.
  /// @param user The address of the user.
  /// @param reserveId The identifier of the reserve.
  event RefreshSingleUserDynamicConfig(address indexed user, uint256 reserveId);

  /// @notice Emitted on setUserPositionManager or renouncePositionManagerRole action.
  /// @param user The address of the user on whose behalf position manager can act.
  /// @param positionManager The address of the position manager.
  /// @param approve True if position manager approval was granted, false if it was revoked.
  event SetUserPositionManager(address indexed user, address indexed positionManager, bool approve);

  /// @notice Emitted on refreshPremiumDebt action.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @param premiumDelta The change in premium values.
  event RefreshPremiumDebt(
    uint256 indexed reserveId,
    address indexed user,
    IHubBase.PremiumDelta premiumDelta
  );

  /// @notice Thrown when an asset is not listed on the Hub when adding a reserve.
  error AssetNotListed();

  /// @notice Thrown when adding a new reserve if that reserve already exists for a given Hub/assetId pair.
  error ReserveExists();

  /// @notice Thrown when adding a new reserve if an asset id is invalid.
  error InvalidAssetId();

  /// @notice Thrown when adding a new reserve if the asset decimals are invalid.
  error InvalidAssetDecimals();

  /// @notice Thrown when updating a reserve if it is not listed.
  error ReserveNotListed();

  /// @notice Thrown when a reserve is not borrowable during a `borrow` action.
  error ReserveNotBorrowable();

  /// @notice Thrown when a reserve is paused during an attempted action.
  error ReservePaused();

  /// @notice Thrown when a reserve is frozen.
  /// @dev Can only occur during an attempted `supply`, `borrow`, or `setUsingAsCollateral` action.
  error ReserveFrozen();

  /// @notice Thrown when an action causes a user's health factor to fall below the liquidation threshold.
  error HealthFactorBelowThreshold();

  /// @notice Thrown when reserve is not enabled as collateral during liquidation.
  error ReserveNotEnabledAsCollateral();

  /// @notice Thrown when a specified reserve is not supplied by the user during liquidation.
  error ReserveNotSupplied();

  /// @notice Thrown when a specified reserve is not borrowed by the user during liquidation.
  error ReserveNotBorrowed();

  /// @notice Thrown when an unauthorized caller attempts an action.
  error Unauthorized();

  /// @notice Thrown if a config key is uninitialized when updating a dynamic reserve config.
  error DynamicConfigKeyUninitialized();

  /// @notice Thrown for an invalid zero address.
  error InvalidAddress();

  /// @notice Thrown when the oracle decimals are not 8 in the constructor.
  error InvalidOracleDecimals();

  /// @notice Thrown when the maximum user reserves limit is zero in the constructor.
  error InvalidMaxUserReservesLimit();

  /// @notice Thrown when a collateral risk exceeds the maximum allowed.
  error InvalidCollateralRisk();

  /// @notice Thrown if a liquidation config is invalid when it is updated.
  error InvalidLiquidationConfig();

  /// @notice Thrown when a liquidation fee is invalid.
  error InvalidLiquidationFee();

  /// @notice Thrown when a collateral factor and max liquidation bonus are invalid.
  error InvalidCollateralFactorAndMaxLiquidationBonus();

  /// @notice Thrown when trying to set zero collateralFactor on historic dynamic configuration keys.
  error InvalidCollateralFactor();

  /// @notice Thrown when a self-liquidation is attempted.
  error SelfLiquidation();

  /// @notice Thrown during liquidation when a user's health factor is not below the liquidation threshold.
  error HealthFactorNotBelowThreshold();

  /// @notice Thrown when collateral or debt dust remains after a liquidation, and neither reserve is fully liquidated.
  error MustNotLeaveDust();

  /// @notice Thrown when a debt to cover input is zero.
  error InvalidDebtToCover();

  /// @notice Thrown when the liquidator tries to receive shares for a collateral reserve that is frozen or is not enabled to receive shares.
  error CannotReceiveShares();

  /// @notice Thrown when the maximum number of dynamic config keys is reached.
  error MaximumDynamicConfigKeyReached();

  /// @notice Thrown when user attempts to exceed either the maximum allowed collateral or borrowed reserves.
  error MaximumUserReservesExceeded();

  /// @notice Updates the liquidation config.
  /// @param config The new liquidation config.
  function updateLiquidationConfig(LiquidationConfig calldata config) external;

  /// @notice Adds a new reserve to the Spoke.
  /// @dev Allowed even if the Spoke has not yet been added to the Hub.
  /// @dev Allowed even if the `active` flag is `false`.
  /// @dev Allowed even if the Spoke has been added but the `addCap` is zero.
  /// @param hub The address of the Hub where the asset is listed.
  /// @param assetId The identifier of the asset in the Hub.
  /// @param priceSource The address of the price source for the asset.
  /// @param config The initial reserve configuration.
  /// @param dynamicConfig The initial dynamic reserve configuration.
  /// @return The identifier of the newly added reserve.
  function addReserve(
    address hub,
    uint256 assetId,
    address priceSource,
    ReserveConfig calldata config,
    DynamicReserveConfig calldata dynamicConfig
  ) external returns (uint256);

  /// @notice Updates the reserve config for a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @param params The new reserve config.
  function updateReserveConfig(uint256 reserveId, ReserveConfig calldata params) external;

  /// @notice Updates the price source of a reserve.
  /// @param reserveId The identifier of the reserve.
  /// @param priceSource The address of the price source.
  function updateReservePriceSource(uint256 reserveId, address priceSource) external;

  /// @notice Updates the dynamic reserve config for a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev Appends dynamic config to the next available key; reverts if `MAX_ALLOWED_DYNAMIC_CONFIG_KEY` is reached.
  /// @param reserveId The identifier of the reserve.
  /// @param dynamicConfig The new dynamic reserve config.
  /// @return dynamicConfigKey The key of the added dynamic config.
  function addDynamicReserveConfig(
    uint256 reserveId,
    DynamicReserveConfig calldata dynamicConfig
  ) external returns (uint32 dynamicConfigKey);

  /// @notice Updates the dynamic reserve config for a given reserve at the specified key.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev Reverts with `DynamicConfigKeyUninitialized` if the config key has not been initialized yet.
  /// @dev Reverts with `InvalidCollateralFactor` if the collateral factor is 0.
  /// @param reserveId The identifier of the reserve.
  /// @param dynamicConfigKey The key of the config to update.
  /// @param dynamicConfig The new dynamic reserve config.
  function updateDynamicReserveConfig(
    uint256 reserveId,
    uint32 dynamicConfigKey,
    DynamicReserveConfig calldata dynamicConfig
  ) external;

  /// @notice Allows an approved caller (admin) to toggle the active status of position manager.
  /// @param positionManager The address of the position manager.
  /// @param active True if positionManager is to be set as active.
  function updatePositionManager(address positionManager, bool active) external;

  /// @notice Supplies an amount of underlying asset of the specified reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev The Spoke pulls the underlying asset from the caller, so prior token approval is required.
  /// @dev Caller must be `onBehalfOf` or an authorized position manager for `onBehalfOf`.
  /// @param reserveId The reserve identifier.
  /// @param amount The amount of asset to supply.
  /// @param onBehalfOf The owner of the position to add supply shares to.
  /// @return The amount of shares supplied.
  /// @return The amount of assets supplied.
  function supply(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external returns (uint256, uint256);

  /// @notice Withdraws a specified amount of underlying asset from the given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev Providing an amount greater than the maximum withdrawable value signals a full withdrawal.
  /// @dev Caller must be `onBehalfOf` or an authorized position manager for `onBehalfOf`.
  /// @dev Caller receives the underlying asset withdrawn.
  /// @param reserveId The identifier of the reserve.
  /// @param amount The amount of asset to withdraw.
  /// @param onBehalfOf The owner of position to remove supply shares from.
  /// @return The amount of shares withdrawn.
  /// @return The amount of assets withdrawn.
  function withdraw(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external returns (uint256, uint256);

  /// @notice Borrows a specified amount of underlying asset from the given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev It reverts if the user would borrow more than the maximum allowed number of borrowed reserves.
  /// @dev Caller must be `onBehalfOf` or an authorized position manager for `onBehalfOf`.
  /// @dev Caller receives the underlying asset borrowed.
  /// @param reserveId The identifier of the reserve.
  /// @param amount The amount of asset to borrow.
  /// @param onBehalfOf The owner of the position against which debt is generated.
  /// @return The amount of shares borrowed.
  /// @return The amount of assets borrowed.
  function borrow(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external returns (uint256, uint256);

  /// @notice Repays a specified amount of underlying asset to a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev The Spoke pulls the underlying asset from the caller, so prior approval is required.
  /// @dev Caller must be `onBehalfOf` or an authorized position manager for `onBehalfOf`.
  /// @param reserveId The identifier of the reserve.
  /// @param amount The amount of asset to repay.
  /// @param onBehalfOf The owner of the position whose debt is repaid.
  /// @return The amount of shares repaid.
  /// @return The amount of assets repaid.
  function repay(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external returns (uint256, uint256);

  /// @notice Liquidates a user position.
  /// @dev It reverts if the reserves associated with any of the given reserve identifiers are not listed.
  /// @dev The Spoke pulls underlying repaid debt assets from caller (Liquidator), hence it needs prior approval.
  /// @param collateralReserveId The reserveId of the underlying asset used as collateral by the liquidated user.
  /// @param debtReserveId The reserveId of the underlying asset borrowed by the liquidated user, to be repaid by Liquidator.
  /// @param user The address of the user to liquidate.
  /// @param debtToCover The desired amount of debt to cover.
  /// @param receiveShares True to receive collateral in supplied shares, false to receive in underlying assets.
  function liquidationCall(
    uint256 collateralReserveId,
    uint256 debtReserveId,
    address user,
    uint256 debtToCover,
    bool receiveShares
  ) external;

  /// @notice Allows suppliers to enable/disable a specific supplied reserve as collateral.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev It reverts if the user exceeds the maximum allowed collateral reserves when enabling.
  /// @dev Reserves with zero supplied or zero collateral factor count towards the max allowed collateral reserves.
  /// @dev Caller must be `onBehalfOf` or an authorized position manager for `onBehalfOf`.
  /// @param reserveId The reserve identifier of the underlying asset.
  /// @param usingAsCollateral True if the user wants to use the supply as collateral.
  /// @param onBehalfOf The owner of the position being modified.
  function setUsingAsCollateral(
    uint256 reserveId,
    bool usingAsCollateral,
    address onBehalfOf
  ) external;

  /// @notice Allows updating the risk premium on onBehalfOf position.
  /// @dev Caller must be `onBehalfOf`, an authorized position manager for `onBehalfOf`, or admin.
  /// @param onBehalfOf The owner of the position being modified.
  function updateUserRiskPremium(address onBehalfOf) external;

  /// @notice Allows updating the dynamic configuration for all collateral reserves on onBehalfOf position.
  /// @dev Caller must be `onBehalfOf`, an authorized position manager for `onBehalfOf`, or admin.
  /// @param onBehalfOf The owner of the position being modified.
  function updateUserDynamicConfig(address onBehalfOf) external;

  /// @notice Enables a user to grant or revoke approval for a position manager.
  /// @dev Allows approving inactive position managers.
  /// @param positionManager The address of the position manager.
  /// @param approve True to approve the position manager, false to revoke approval.
  function setUserPositionManager(address positionManager, bool approve) external;

  /// @notice Enables a user to grant or revoke approval for an array of position managers using an EIP712-typed intent.
  /// @dev Uses keyed-nonces where for each key's namespace nonce is consumed sequentially.
  /// @dev Allows duplicated updates and the last one is persisted. Allows approving inactive position managers.
  /// @param params The structured setUserPositionManagers parameter.
  /// @param signature The EIP712-compliant signature bytes.
  function setUserPositionManagersWithSig(
    SetUserPositionManagers calldata params,
    bytes calldata signature
  ) external;

  /// @notice Allows position manager (as caller) to renounce their approval given by the user.
  /// @param user The address of the user.
  function renouncePositionManagerRole(address user) external;

  /// @notice Allows consuming a permit signature for the given reserve's underlying asset.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev The Spoke must be configured as the spender.
  /// @param reserveId The identifier of the reserve.
  /// @param onBehalfOf The address of the user on whose behalf the permit is being used.
  /// @param value The amount of the underlying asset to permit.
  /// @param deadline The deadline for the permit.
  /// @param permitV The v parameter of the permit signature.
  /// @param permitR The r parameter of the permit signature.
  /// @param permitS The s parameter of the permit signature.
  function permitReserve(
    uint256 reserveId,
    address onBehalfOf,
    uint256 value,
    uint256 deadline,
    uint8 permitV,
    bytes32 permitR,
    bytes32 permitS
  ) external;

  /// @notice Returns the liquidation config struct.
  function getLiquidationConfig() external view returns (LiquidationConfig memory);

  /// @notice Returns the number of listed reserves on the Spoke.
  /// @dev Count includes reserves that are not currently active.
  function getReserveCount() external view returns (uint256);

  /// @notice Returns the total amount of supplied assets of a given reserve.
  /// @param reserveId The identifier of the reserve.
  /// @return The amount of supplied assets.
  function getReserveSuppliedAssets(uint256 reserveId) external view returns (uint256);

  /// @notice Returns the total amount of supplied shares of a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @return The amount of supplied shares.
  function getReserveSuppliedShares(uint256 reserveId) external view returns (uint256);

  /// @notice Returns the debt of a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev The total debt of the reserve is the sum of drawn debt and premium debt.
  /// @param reserveId The identifier of the reserve.
  /// @return The amount of drawn debt.
  /// @return The amount of premium debt.
  function getReserveDebt(uint256 reserveId) external view returns (uint256, uint256);

  /// @notice Returns the total debt of a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev The total debt of the reserve is the sum of drawn debt and premium debt.
  /// @param reserveId The identifier of the reserve.
  /// @return The total debt amount.
  function getReserveTotalDebt(uint256 reserveId) external view returns (uint256);

  /// @notice Returns the reserve identifier for a given asset in a Hub.
  /// @dev It reverts if no reserve is associated with the given asset identifier.
  /// @param hub The address of the Hub.
  /// @param assetId The identifier of the asset on the Hub.
  /// @return The identifier of the reserve.
  function getReserveId(address hub, uint256 assetId) external view returns (uint256);

  /// @notice Returns the reserve struct data in storage.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @return The reserve struct.
  function getReserve(uint256 reserveId) external view returns (Reserve memory);

  /// @notice Returns the reserve configuration struct data in storage.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @return The reserve configuration struct.
  function getReserveConfig(uint256 reserveId) external view returns (ReserveConfig memory);

  /// @notice Returns the dynamic reserve configuration struct at the specified key.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev Does not revert if `dynamicConfigKey` is unset.
  /// @param reserveId The identifier of the reserve.
  /// @param dynamicConfigKey The key of the dynamic config.
  /// @return The dynamic reserve configuration struct.
  function getDynamicReserveConfig(
    uint256 reserveId,
    uint32 dynamicConfigKey
  ) external view returns (DynamicReserveConfig memory);

  /// @notice Returns two flags indicating whether the reserve is used as collateral and whether it is borrowed by the user.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev Even if enabled as collateral, it will only count towards user position if the collateral factor is greater than 0.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @return True if the reserve is enabled as collateral by the user.
  /// @return True if the reserve is borrowed by the user.
  function getUserReserveStatus(uint256 reserveId, address user) external view returns (bool, bool);

  /// @notice Returns the amount of assets supplied by a specific user for a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @return The amount of assets supplied by the user.
  function getUserSuppliedAssets(uint256 reserveId, address user) external view returns (uint256);

  /// @notice Returns the amount of shares supplied by a specific user for a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @return The amount of shares supplied by the user.
  function getUserSuppliedShares(uint256 reserveId, address user) external view returns (uint256);

  /// @notice Returns the debt of a specific user for a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev The total debt of the user is the sum of drawn debt and premium debt.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @return The amount of drawn debt.
  /// @return The amount of premium debt.
  function getUserDebt(uint256 reserveId, address user) external view returns (uint256, uint256);

  /// @notice Returns the total debt of a specific user for a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @dev The total debt of the user is the sum of drawn debt and premium debt.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @return The total debt amount.
  function getUserTotalDebt(uint256 reserveId, address user) external view returns (uint256);

  /// @notice Returns the full precision premium debt of a specific user for a given reserve.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @return The amount of premium debt, expressed in asset units and scaled by RAY.
  function getUserPremiumDebtRay(uint256 reserveId, address user) external view returns (uint256);

  /// @notice Returns the user position struct in storage.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @return The user position struct.
  function getUserPosition(
    uint256 reserveId,
    address user
  ) external view returns (UserPosition memory);

  /// @notice Returns the most up-to-date user account data information.
  /// @dev Utilizes user's current dynamic configuration of user position.
  /// @param user The address of the user.
  /// @return The user account data struct.
  function getUserAccountData(address user) external view returns (UserAccountData memory);

  /// @notice Returns the risk premium from the user's last position update.
  /// @param user The address of the user.
  /// @return The risk premium of the user from the last position update, expressed in BPS.
  function getUserLastRiskPremium(address user) external view returns (uint256);

  /// @notice Returns the liquidation bonus for a given health factor, based on the user's current dynamic configuration.
  /// @dev It reverts if the reserve associated with the given reserve identifier is not listed.
  /// @param reserveId The identifier of the reserve.
  /// @param user The address of the user.
  /// @param healthFactor The health factor of the user, expressed in WAD.
  /// @return The liquidation bonus for the user, expressed in BPS.
  function getLiquidationBonus(
    uint256 reserveId,
    address user,
    uint256 healthFactor
  ) external view returns (uint256);

  /// @notice Returns whether positionManager is currently activated by governance.
  /// @param positionManager The address of the position manager.
  /// @return True if positionManager is currently active.
  function isPositionManagerActive(address positionManager) external view returns (bool);

  /// @notice Returns whether positionManager is active and approved by user.
  /// @param user The address of the user.
  /// @param positionManager The address of the position manager.
  /// @return True if positionManager is active and approved by user.
  function isPositionManager(address user, address positionManager) external view returns (bool);

  /// @notice Returns the address of the external `LiquidationLogic` library.
  function getLiquidationLogic() external pure returns (address);

  /// @notice Returns the type hash for the SetUserPositionManagers intent.
  /// @return The bytes-encoded EIP-712 struct hash representing the intent.
  function SET_USER_POSITION_MANAGERS_TYPEHASH() external view returns (bytes32);

  /// @notice Returns the address of the AaveOracle contract.
  function ORACLE() external view returns (address);

  /// @notice Returns the maximum allowed number of collateral and borrow reserves per user (each counted separately).
  function MAX_USER_RESERVES_LIMIT() external view returns (uint16);
}

// src/spoke/libraries/ReserveFlagsMap.sol

/// @title ReserveFlags Library
/// @author Aave Labs
/// @notice Implements the bitmap logic to handle the Reserve flags configuration.
library ReserveFlagsMap {
  /// @dev Mask for the `paused` flag.
  uint8 internal constant PAUSED_MASK = 0x01;
  /// @dev Mask for the `frozen` flag.
  uint8 internal constant FROZEN_MASK = 0x02;
  /// @dev Mask for the `borrowable` flag.
  uint8 internal constant BORROWABLE_MASK = 0x04;
  /// @dev Mask for the `receiveSharesEnabled` flag.
  uint8 internal constant RECEIVE_SHARES_ENABLED_MASK = 0x08;

  /// @notice Initializes the ReserveFlags with the given values.
  /// @param initPaused The initial `paused` flag status.
  /// @param initFrozen The initial `frozen` flag status.
  /// @param initBorrowable The initial `borrowable` flag status.
  /// @param initReceiveSharesEnabled The initial `receiveSharesEnabled` flag status.
  /// @return The initialized ReserveFlags.
  function create(
    bool initPaused,
    bool initFrozen,
    bool initBorrowable,
    bool initReceiveSharesEnabled
  ) internal pure returns (ReserveFlags) {
    uint8 flags = 0;
    flags = _setStatus(flags, PAUSED_MASK, initPaused);
    flags = _setStatus(flags, FROZEN_MASK, initFrozen);
    flags = _setStatus(flags, BORROWABLE_MASK, initBorrowable);
    flags = _setStatus(flags, RECEIVE_SHARES_ENABLED_MASK, initReceiveSharesEnabled);
    return ReserveFlags.wrap(flags);
  }

  /// @notice Sets the new status for the `paused` flag.
  /// @param flags The current ReserveFlags.
  /// @param status The new status for the `paused` flag.
  /// @return The updated ReserveFlags.
  function setPaused(ReserveFlags flags, bool status) internal pure returns (ReserveFlags) {
    return ReserveFlags.wrap(_setStatus(ReserveFlags.unwrap(flags), PAUSED_MASK, status));
  }

  /// @notice Sets the new status for the `frozen` flag.
  /// @param flags The current ReserveFlags.
  /// @param status The new status for the `frozen` flag.
  /// @return The updated ReserveFlags.
  function setFrozen(ReserveFlags flags, bool status) internal pure returns (ReserveFlags) {
    return ReserveFlags.wrap(_setStatus(ReserveFlags.unwrap(flags), FROZEN_MASK, status));
  }

  /// @notice Sets the new status for the `borrowable` flag.
  /// @param flags The current ReserveFlags.
  /// @param status The new status for the `borrowable` flag.
  /// @return The updated ReserveFlags.
  function setBorrowable(ReserveFlags flags, bool status) internal pure returns (ReserveFlags) {
    return ReserveFlags.wrap(_setStatus(ReserveFlags.unwrap(flags), BORROWABLE_MASK, status));
  }

  /// @notice Sets the new status for the `receiveSharesEnabled` flag.
  /// @param flags The current ReserveFlags.
  /// @param status The new status for the `receiveSharesEnabled` flag.
  /// @return The updated ReserveFlags.
  function setReceiveSharesEnabled(
    ReserveFlags flags,
    bool status
  ) internal pure returns (ReserveFlags) {
    return
      ReserveFlags.wrap(
        _setStatus(ReserveFlags.unwrap(flags), RECEIVE_SHARES_ENABLED_MASK, status)
      );
  }

  /// @notice Returns the `paused` flag status.
  /// @param flags The current ReserveFlags.
  /// @return True if the flag is set.
  function paused(ReserveFlags flags) internal pure returns (bool) {
    return (ReserveFlags.unwrap(flags) & PAUSED_MASK) != 0;
  }

  /// @notice Returns the `frozen` flag status.
  /// @param flags The current ReserveFlags.
  /// @return True if the flag is set.
  function frozen(ReserveFlags flags) internal pure returns (bool) {
    return (ReserveFlags.unwrap(flags) & FROZEN_MASK) != 0;
  }

  /// @notice Returns the `borrowable` flag status.
  /// @param flags The current ReserveFlags.
  /// @return True if the flag is set.
  function borrowable(ReserveFlags flags) internal pure returns (bool) {
    return (ReserveFlags.unwrap(flags) & BORROWABLE_MASK) != 0;
  }

  /// @notice Returns the `receiveSharesEnabled` flag status.
  /// @param flags The current ReserveFlags.
  /// @return True if the flag is set.
  function receiveSharesEnabled(ReserveFlags flags) internal pure returns (bool) {
    return (ReserveFlags.unwrap(flags) & RECEIVE_SHARES_ENABLED_MASK) != 0;
  }

  /// @notice Sets the new status for the given flag.
  function _setStatus(uint8 flags, uint8 mask, bool status) private pure returns (uint8) {
    return status ? flags | mask : flags & ~mask;
  }
}

// src/spoke/libraries/PositionStatusMap.sol

/// @title PositionStatusMap Library
/// @author Aave Labs
/// @notice Implements the bitmap logic to handle the user configuration.
library PositionStatusMap {
  using PositionStatusMap for *;
  using LibBit for uint256;

  uint256 internal constant NOT_FOUND = type(uint256).max;

  uint256 internal constant BORROWING_MASK =
    0x5555555555555555555555555555555555555555555555555555555555555555;
  uint256 internal constant COLLATERAL_MASK =
    0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;

  /// @notice Sets if the user is borrowing the specified reserve.
  function setBorrowing(
    ISpoke.PositionStatus storage self,
    uint256 reserveId,
    bool borrowing
  ) internal {
    unchecked {
      uint256 bit = 1 << ((reserveId % 128) << 1);
      if (borrowing) {
        self.map[reserveId.bucketId()] |= bit;
      } else {
        self.map[reserveId.bucketId()] &= ~bit;
      }
    }
  }

  /// @notice Sets if the user is using as collateral the specified reserve.
  function setUsingAsCollateral(
    ISpoke.PositionStatus storage self,
    uint256 reserveId,
    bool usingAsCollateral
  ) internal {
    unchecked {
      uint256 bit = 1 << (((reserveId % 128) << 1) + 1);
      if (usingAsCollateral) {
        self.map[reserveId.bucketId()] |= bit;
      } else {
        self.map[reserveId.bucketId()] &= ~bit;
      }
    }
  }

  /// @notice Returns if a user is using the specified reserve for borrowing or as collateral.
  function isUsingAsCollateralOrBorrowing(
    ISpoke.PositionStatus storage self,
    uint256 reserveId
  ) internal view returns (bool) {
    unchecked {
      return (self.getBucketWord(reserveId) >> ((reserveId % 128) << 1)) & 3 != 0;
    }
  }

  /// @notice Returns if a user is using the specified reserve for borrowing.
  function isBorrowing(
    ISpoke.PositionStatus storage self,
    uint256 reserveId
  ) internal view returns (bool) {
    unchecked {
      return (self.getBucketWord(reserveId) >> ((reserveId % 128) << 1)) & 1 != 0;
    }
  }

  /// @notice Returns if a user is using the specified reserve as collateral.
  function isUsingAsCollateral(
    ISpoke.PositionStatus storage self,
    uint256 reserveId
  ) internal view returns (bool) {
    unchecked {
      return (self.getBucketWord(reserveId) >> (((reserveId % 128) << 1) + 1)) & 1 != 0;
    }
  }

  /// @notice Counts the number of reserves enabled as collateral.
  /// @dev Disregards potential dirty bits set after `reserveCount`.
  /// @param reserveCount The current `reserveCount`, to avoid reading uninitialized buckets.
  function collateralCount(
    ISpoke.PositionStatus storage self,
    uint256 reserveCount
  ) internal view returns (uint256) {
    unchecked {
      uint256 bucket = reserveCount.bucketId();
      uint256 count = self.map[bucket].isolateCollateralUntil(reserveCount).popCount();
      while (bucket != 0) {
        count += self.map[--bucket].isolateCollateral().popCount();
      }
      return count;
    }
  }

  /// @notice Counts the number of reserves borrowed.
  /// @dev Disregards potential dirty bits set after `reserveCount`.
  /// @param reserveCount The current `reserveCount`, to avoid reading uninitialized buckets.
  function borrowCount(
    ISpoke.PositionStatus storage self,
    uint256 reserveCount
  ) internal view returns (uint256) {
    unchecked {
      uint256 bucket = reserveCount.bucketId();
      uint256 count = self.map[bucket].isolateBorrowingUntil(reserveCount).popCount();
      while (bucket != 0) {
        count += self.map[--bucket].isolateBorrowing().popCount();
      }
      return count;
    }
  }

  /// @notice Finds the previous borrowing or collateralized reserve strictly before `fromReserveId`.
  /// @dev The search starts at `fromReserveId` (exclusive) and scans backward across buckets.
  /// @dev Returns `NOT_FOUND` if no borrowing or collateralized reserve exists before the bound.
  /// @dev Ignores dirty bits beyond the configured `reserveCount` within the last bucket.
  /// @param fromReserveId The identifier of the reserve to start searching from.
  /// @return reserveId The reserve identifier for the next reserve that is borrowed or used as collateral.
  /// @return borrowing True if the next reserveId is borrowed.
  /// @return collateral True if the next reserveId is used as collateral.
  function next(
    ISpoke.PositionStatus storage self,
    uint256 fromReserveId
  ) internal view returns (uint256, bool, bool) {
    unchecked {
      uint256 bucket = fromReserveId.bucketId();
      uint256 map = self.map[bucket];
      uint256 setBitId = map.isolateUntil(fromReserveId).fls();
      while (setBitId == 256 && bucket != 0) {
        map = self.map[--bucket];
        setBitId = map.fls();
      }
      if (setBitId == 256) {
        return (NOT_FOUND, false, false);
      } else {
        uint256 word = map >> ((setBitId >> 1) << 1);
        return (setBitId.fromBitId(bucket), word & 1 != 0, word & 2 != 0);
      }
    }
  }

  /// @notice Finds the previous borrowed reserve strictly before `fromReserveId`.
  /// @dev The search starts at `fromReserveId` (exclusive) and scans backward across buckets.
  /// @dev Returns `NOT_FOUND` if no borrowed reserve exists before the bound.
  /// @dev Ignores dirty bits beyond the configured `reserveCount` within the last bucket.
  /// @param fromReserveId The exclusive upper bound to start from (this reserveId is not considered).
  /// @return The previous borrowed reserveId, or `NOT_FOUND` if none is found.
  function nextBorrowing(
    ISpoke.PositionStatus storage self,
    uint256 fromReserveId
  ) internal view returns (uint256) {
    unchecked {
      uint256 bucket = fromReserveId.bucketId();
      uint256 setBitId = self.map[bucket].isolateBorrowingUntil(fromReserveId).fls();
      while (setBitId == 256 && bucket != 0) {
        setBitId = self.map[--bucket].isolateBorrowing().fls();
      }
      return setBitId == 256 ? NOT_FOUND : setBitId.fromBitId(bucket);
    }
  }

  /// @notice Finds the previous collateral reserve strictly before `fromReserveId`.
  /// @dev The search starts at `fromReserveId` (exclusive) and scans backward across buckets.
  /// @dev Returns `NOT_FOUND` if no collateral reserve exists before the bound.
  /// @dev Ignores dirty bits beyond the configured `reserveCount` within the last bucket.
  /// @param fromReserveId The exclusive upper bound to start from (this reserveId is not considered).
  /// @return The previous collateral reserveId, or `NOT_FOUND` if none is found.
  function nextCollateral(
    ISpoke.PositionStatus storage self,
    uint256 fromReserveId
  ) internal view returns (uint256) {
    unchecked {
      uint256 bucket = fromReserveId.bucketId();
      uint256 setBitId = self.map[bucket].isolateCollateralUntil(fromReserveId).fls();
      while (setBitId == 256 && bucket != 0) {
        setBitId = self.map[--bucket].isolateCollateral().fls();
      }
      return setBitId == 256 ? NOT_FOUND : setBitId.fromBitId(bucket);
    }
  }

  /// @notice Returns the word containing the reserve state in the bitmap.
  function getBucketWord(
    ISpoke.PositionStatus storage self,
    uint256 reserveId
  ) internal view returns (uint256) {
    return self.map[reserveId.bucketId()];
  }

  /// @notice Converts a reserveId to its corresponding bucketId.
  function bucketId(uint256 reserveId) internal pure returns (uint256 wordId) {
    assembly ('memory-safe') {
      wordId := shr(7, reserveId)
    }
  }

  /// @notice Converts a bit index to its corresponding reserve index in the bitmap.
  /// @dev BitId 0, 1 correspond to reserveId 0; BitId 2, 3 correspond to reserveId 1; etc.
  function fromBitId(uint256 bitId, uint256 bucket) internal pure returns (uint256 reserveId) {
    assembly ('memory-safe') {
      reserveId := add(shr(1, bitId), shl(7, bucket))
    }
  }

  /// @notice Isolates the borrowing bits from word.
  function isolateBorrowing(uint256 word) internal pure returns (uint256 ret) {
    assembly ('memory-safe') {
      ret := and(word, BORROWING_MASK)
    }
  }

  /// @notice Returns masked `word` containing only borrowing bits from the first reserve up to `reserveCount`.
  function isolateBorrowingUntil(
    uint256 word,
    uint256 reserveCount
  ) internal pure returns (uint256 ret) {
    // ret = word & (BORROWING_MASK >> (256 - ((reserveCount % 128) << 1)));
    assembly ('memory-safe') {
      ret := and(word, shr(sub(256, shl(1, mod(reserveCount, 128))), BORROWING_MASK))
    }
  }

  /// @notice Returns masked `word` containing bits from the first reserve up to `reserveCount`.
  function isolateUntil(uint256 word, uint256 reserveCount) internal pure returns (uint256 ret) {
    // ret = word & (type(uint256).max >> (256 - ((reserveCount % 128) << 1)));
    assembly ('memory-safe') {
      ret := and(word, shr(sub(256, shl(1, mod(reserveCount, 128))), not(0)))
    }
  }

  /// @notice Isolates the collateral bits from word.
  function isolateCollateral(uint256 word) internal pure returns (uint256 ret) {
    assembly ('memory-safe') {
      ret := and(word, COLLATERAL_MASK)
    }
  }

  /// @notice Returns masked `word` containing only collateral bits from the first reserve up to `reserveCount`.
  function isolateCollateralUntil(
    uint256 word,
    uint256 reserveCount
  ) internal pure returns (uint256 ret) {
    // ret = word & (COLLATERAL_MASK >> (256 - ((reserveCount % 128) << 1)));
    assembly ('memory-safe') {
      ret := and(word, shr(sub(256, shl(1, mod(reserveCount, 128))), COLLATERAL_MASK))
    }
  }
}

// src/spoke/libraries/SpokeUtils.sol

/// @title SpokeUtils library
/// @author Aave Labs
/// @notice Provides utility functions for the Spoke contract.
library SpokeUtils {
  /// @dev See Spoke.ORACLE_DECIMALS docs
  uint8 public constant ORACLE_DECIMALS = 8;

  /// @notice Returns the reserve for a given reserve id.
  /// @param reserves The mapping of reserves per reserve id.
  /// @param reserveId The identifier of the reserve.
  /// @return The reserve.
  function get(
    mapping(uint256 reserveId => ISpoke.Reserve) storage reserves,
    uint256 reserveId
  ) internal view returns (ISpoke.Reserve storage) {
    ISpoke.Reserve storage reserve = reserves[reserveId];
    require(address(reserve.hub) != address(0), ISpoke.ReserveNotListed());
    return reserve;
  }

  /// @notice Converts an asset amount to Value. 1e26 represents 1 USD.
  /// @dev Reverts if asset uses more than 18 decimals. Reverts if multiplication overflows.
  /// @param amount The asset amount.
  /// @param decimals The decimals of the asset.
  /// @param price The price of the asset.
  /// @return The amount in units of Value.
  function toValue(
    uint256 amount,
    uint256 decimals,
    uint256 price
  ) internal pure returns (uint256) {
    return amount * price * MathUtils.uncheckedExp(10, WadRayMath.WAD_DECIMALS - decimals);
  }
}

// src/spoke/libraries/UserPositionUtils.sol

/// @title User Debt library
/// @author Aave Labs
/// @notice Implements debt calculations for user positions.
library UserPositionUtils {
  using UserPositionUtils for ISpoke.UserPosition;
  using SafeCast for *;
  using PercentageMath for uint256;
  using WadRayMath for *;
  using MathUtils for *;

  /// @notice Debt components of a user position.
  /// @dev drawnShares The amount of drawn shares.
  /// @dev premiumDebtRay The amount of premium debt, expressed in asset units and scaled by RAY.
  /// @dev drawnIndex The drawn index of the reserve, expressed in RAY.
  struct DebtComponents {
    uint256 drawnShares;
    uint256 premiumDebtRay;
    uint256 drawnIndex;
  }

  /// @notice Applies the premium delta to the user position.
  /// @param userPosition The user position.
  /// @param premiumDelta The premium delta to apply.
  function applyPremiumDelta(
    ISpoke.UserPosition storage userPosition,
    IHubBase.PremiumDelta memory premiumDelta
  ) internal {
    userPosition.premiumShares = userPosition
      .premiumShares
      .add(premiumDelta.sharesDelta)
      .toUint120();
    userPosition.premiumOffsetRay = (userPosition.premiumOffsetRay + premiumDelta.offsetRayDelta)
      .toInt200();
  }

  /// @notice Calculates the premium delta for a user position given a new risk premium.
  /// @param userPosition The user position.
  /// @param drawnSharesTaken The amount of drawn shares taken from the user position.
  /// @param drawnIndex The current drawn index.
  /// @param riskPremium The new risk premium, expressed in BPS.
  /// @param restoredPremiumRay The amount of premium to be restored, expressed in asset units and scaled by RAY.
  /// @return The calculated premium delta.
  function calculatePremiumDelta(
    ISpoke.UserPosition storage userPosition,
    uint256 drawnSharesTaken,
    uint256 drawnIndex,
    uint256 riskPremium,
    uint256 restoredPremiumRay
  ) internal view returns (IHubBase.PremiumDelta memory) {
    uint256 oldPremiumShares = userPosition.premiumShares;
    int256 oldPremiumOffsetRay = userPosition.premiumOffsetRay;
    uint256 premiumDebtRay = Premium.calculatePremiumRay({
      premiumShares: oldPremiumShares,
      premiumOffsetRay: oldPremiumOffsetRay,
      drawnIndex: drawnIndex
    });
    uint256 newPremiumShares = (userPosition.drawnShares - drawnSharesTaken).percentMulUp(
      riskPremium
    );
    int256 newPremiumOffsetRay = (newPremiumShares * drawnIndex).signedSub(
      premiumDebtRay - restoredPremiumRay
    );

    return
      IHubBase.PremiumDelta({
        sharesDelta: newPremiumShares.signedSub(oldPremiumShares),
        offsetRayDelta: newPremiumOffsetRay - oldPremiumOffsetRay,
        restoredPremiumRay: restoredPremiumRay
      });
  }

  /// @dev Calculates the drawn debt and premium debt to restore for the given user position and amount.
  /// @param userPosition The user position.
  /// @param drawnIndex The drawn index of the reserve.
  /// @param amount The amount to restore.
  /// @return The amount of drawn debt to restore, expressed in asset units.
  /// @return The amount of premium debt to restore, expressed in asset units and scaled by RAY.
  function calculateRestoreAmount(
    ISpoke.UserPosition storage userPosition,
    uint256 drawnIndex,
    uint256 amount
  ) internal view returns (uint256, uint256) {
    (uint256 drawnDebt, uint256 premiumDebtRay) = userPosition.getDebt(drawnIndex);
    uint256 premiumDebt = premiumDebtRay.fromRayUp();
    if (amount >= drawnDebt + premiumDebt) {
      return (drawnDebt, premiumDebtRay);
    }

    if (amount < premiumDebt) {
      // amount.toRay() cannot overflow here
      uint256 amountRay = amount.toRay();
      return (0, amountRay);
    }
    return (amount - premiumDebt, premiumDebtRay);
  }

  /// @notice Calculates the user's debt based on the latest drawn index of the Hub asset.
  /// @param userPosition The user position.
  /// @param hub The address of the Hub.
  /// @param assetId The identifier of the asset.
  /// @return The user's drawn debt, expressed in asset units.
  /// @return The user's premium debt, expressed in asset units and scaled by RAY.
  function getDebt(
    ISpoke.UserPosition storage userPosition,
    IHubBase hub,
    uint256 assetId
  ) internal view returns (uint256, uint256) {
    return userPosition.getDebt(hub.getAssetDrawnIndex(assetId));
  }

  /// @notice Calculates the user's debt based on the specified drawn index of the Hub asset.
  /// @param userPosition The user position.
  /// @param drawnIndex The drawn index of the reserve, expressed in RAY.
  /// @return The user's drawn debt, expressed in asset units.
  /// @return The user's premium debt, expressed in asset units and scaled by RAY.
  function getDebt(
    ISpoke.UserPosition storage userPosition,
    uint256 drawnIndex
  ) internal view returns (uint256, uint256) {
    uint256 premiumDebtRay = _calculatePremiumRay(userPosition, drawnIndex);
    return (userPosition.drawnShares.rayMulUp(drawnIndex), premiumDebtRay);
  }

  /// @notice Calculates the debt components of the user position.
  function getDebtComponents(
    ISpoke.UserPosition storage userPosition,
    IHubBase hub,
    uint256 assetId
  ) internal view returns (DebtComponents memory) {
    uint256 drawnIndex = hub.getAssetDrawnIndex(assetId);
    return
      DebtComponents({
        drawnShares: userPosition.drawnShares,
        premiumDebtRay: _calculatePremiumRay(userPosition, drawnIndex),
        drawnIndex: drawnIndex
      });
  }

  /// @dev Calculates the premium debt of a user position with full precision.
  /// @param userPosition The user position.
  /// @param drawnIndex The current drawn index.
  /// @return The premium debt, expressed in asset units and scaled by RAY.
  function _calculatePremiumRay(
    ISpoke.UserPosition storage userPosition,
    uint256 drawnIndex
  ) internal view returns (uint256) {
    return
      Premium.calculatePremiumRay({
        premiumShares: userPosition.premiumShares,
        premiumOffsetRay: userPosition.premiumOffsetRay,
        drawnIndex: drawnIndex
      });
  }
}

// src/spoke/libraries/LiquidationLogic.sol

/// @title LiquidationLogic library
/// @author Aave Labs
/// @notice Implements the logic for liquidations.
library LiquidationLogic {
  using SafeCast for *;
  using SafeERC20 for IERC20;
  using MathUtils for *;
  using PercentageMath for uint256;
  using WadRayMath for uint256;
  using SpokeUtils for *;
  using UserPositionUtils for ISpoke.UserPosition;
  using ReserveFlagsMap for ReserveFlags;
  using PositionStatusMap for ISpoke.PositionStatus;

  struct LiquidateUserParams {
    uint256 collateralReserveId;
    uint256 debtReserveId;
    address oracle;
    address user;
    ISpoke.LiquidationConfig liquidationConfig;
    uint256 debtToCover;
    ISpoke.UserAccountData userAccountData;
    address liquidator;
    bool receiveShares;
  }

  struct ExecuteLiquidationParams {
    IHubBase collateralHub;
    uint256 collateralAssetId;
    uint256 collateralAssetDecimals;
    uint256 collateralReserveId;
    ReserveFlags collateralReserveFlags;
    ISpoke.DynamicReserveConfig collateralDynConfig;
    IHubBase debtHub;
    uint256 debtAssetId;
    uint256 debtAssetDecimals;
    address debtUnderlying;
    uint256 debtReserveId;
    ReserveFlags debtReserveFlags;
    ISpoke.LiquidationConfig liquidationConfig;
    address oracle;
    address user;
    uint256 debtToCover;
    uint256 healthFactor;
    uint256 totalDebtValueRay;
    uint256 activeCollateralCount;
    uint256 borrowCount;
    address liquidator;
    bool receiveShares;
  }

  struct LiquidateCollateralParams {
    IHubBase hub;
    uint256 assetId;
    uint256 sharesToLiquidate;
    uint256 sharesToLiquidator;
    address liquidator;
    bool receiveShares;
  }

  struct LiquidateCollateralResult {
    uint256 amountRemoved;
    bool isCollateralPositionEmpty;
  }

  struct LiquidateDebtParams {
    IHubBase hub;
    uint256 assetId;
    address underlying;
    uint256 reserveId;
    uint256 drawnSharesToLiquidate;
    uint256 premiumDebtRayToLiquidate;
    uint256 drawnIndex;
    address liquidator;
  }

  struct LiquidateDebtResult {
    uint256 amountRestored;
    IHubBase.PremiumDelta premiumDelta;
    bool isDebtPositionEmpty;
  }

  struct ValidateLiquidationCallParams {
    address user;
    address liquidator;
    ReserveFlags collateralReserveFlags;
    ReserveFlags debtReserveFlags;
    uint256 suppliedShares;
    uint256 drawnShares;
    uint256 debtToCover;
    uint256 collateralFactor;
    bool isUsingAsCollateral;
    uint256 healthFactor;
    bool receiveShares;
  }

  struct CalculateDebtToTargetHealthFactorParams {
    uint256 totalDebtValueRay;
    uint256 debtAssetUnit;
    uint256 debtAssetPrice;
    uint256 collateralFactor;
    uint256 liquidationBonus;
    uint256 healthFactor;
    uint256 targetHealthFactor;
  }

  struct CalculateDebtToLiquidateParams {
    uint256 drawnShares;
    uint256 premiumDebtRay;
    uint256 drawnIndex;
    uint256 totalDebtValueRay;
    uint256 debtAssetDecimals;
    uint256 debtAssetUnit;
    uint256 debtAssetPrice;
    uint256 debtToCover;
    uint256 collateralFactor;
    uint256 liquidationBonus;
    uint256 healthFactor;
    uint256 targetHealthFactor;
  }

  struct CalculateCollateralToLiquidateParams {
    IHubBase collateralReserveHub;
    uint256 collateralReserveAssetId;
    uint256 collateralAssetUnit;
    uint256 collateralAssetPrice;
    uint256 drawnSharesToLiquidate;
    uint256 premiumDebtRayToLiquidate;
    uint256 drawnIndex;
    uint256 debtAssetUnit;
    uint256 debtAssetPrice;
    uint256 liquidationBonus;
  }

  struct CalculateLiquidationAmountsParams {
    IHubBase collateralReserveHub;
    uint256 collateralReserveAssetId;
    uint256 suppliedShares;
    uint256 collateralAssetDecimals;
    uint256 collateralAssetPrice;
    uint256 drawnShares;
    uint256 premiumDebtRay;
    uint256 drawnIndex;
    uint256 totalDebtValueRay;
    uint256 debtAssetDecimals;
    uint256 debtAssetPrice;
    uint256 debtToCover;
    uint256 collateralFactor;
    uint256 healthFactorForMaxBonus;
    uint256 liquidationBonusFactor;
    uint256 maxLiquidationBonus;
    uint256 targetHealthFactor;
    uint256 healthFactor;
    uint256 liquidationFee;
  }

  struct LiquidationAmounts {
    uint256 collateralSharesToLiquidate;
    uint256 collateralSharesToLiquidator;
    uint256 drawnSharesToLiquidate;
    uint256 premiumDebtRayToLiquidate;
  }

  /// @dev See Spoke.HEALTH_FACTOR_LIQUIDATION_THRESHOLD docs
  uint64 public constant HEALTH_FACTOR_LIQUIDATION_THRESHOLD = 1e18;

  /// @dev See Spoke.DUST_LIQUIDATION_THRESHOLD docs
  uint256 public constant DUST_LIQUIDATION_THRESHOLD = 1000e26;

  /// @notice Liquidates a user position.
  /// @param reserves The mapping of reserves per reserve id.
  /// @param userPositions The mapping of user positions per user per reserve.
  /// @param positionStatus The mapping of position status per user.
  /// @param dynamicConfig The mapping of dynamic config per reserve per dynamic config key.
  /// @param params The liquidate user params.
  /// @return True if the liquidation results in deficit.
  function liquidateUser(
    mapping(uint256 reserveId => ISpoke.Reserve) storage reserves,
    mapping(address user => mapping(uint256 reserveId => ISpoke.UserPosition)) storage userPositions,
    mapping(address user => ISpoke.PositionStatus) storage positionStatus,
    mapping(uint256 reserveId => mapping(uint32 dynamicConfigKey => ISpoke.DynamicReserveConfig)) storage dynamicConfig,
    LiquidateUserParams memory params
  ) external returns (bool) {
    ISpoke.Reserve storage collateralReserve = reserves.get(params.collateralReserveId);
    ISpoke.Reserve storage debtReserve = reserves.get(params.debtReserveId);

    ISpoke.UserPosition storage collateralUserPosition = userPositions[params.user][
      params.collateralReserveId
    ];
    ISpoke.DynamicReserveConfig storage collateralDynConfig = dynamicConfig[
      params.collateralReserveId
    ][collateralUserPosition.dynamicConfigKey];

    ExecuteLiquidationParams memory executeLiquidationParams = ExecuteLiquidationParams({
      collateralHub: collateralReserve.hub,
      collateralAssetId: collateralReserve.assetId,
      collateralAssetDecimals: collateralReserve.decimals,
      collateralReserveId: params.collateralReserveId,
      collateralReserveFlags: collateralReserve.flags,
      collateralDynConfig: collateralDynConfig,
      debtHub: debtReserve.hub,
      debtAssetId: debtReserve.assetId,
      debtAssetDecimals: debtReserve.decimals,
      debtUnderlying: debtReserve.underlying,
      debtReserveId: params.debtReserveId,
      debtReserveFlags: debtReserve.flags,
      liquidationConfig: params.liquidationConfig,
      oracle: params.oracle,
      user: params.user,
      debtToCover: params.debtToCover,
      healthFactor: params.userAccountData.healthFactor,
      totalDebtValueRay: params.userAccountData.totalDebtValueRay,
      activeCollateralCount: params.userAccountData.activeCollateralCount,
      borrowCount: params.userAccountData.borrowCount,
      liquidator: params.liquidator,
      receiveShares: params.receiveShares
    });

    ISpoke.UserPosition storage debtUserPosition = userPositions[params.user][params.debtReserveId];
    ISpoke.UserPosition storage collateralLiquidatorPosition = userPositions[params.liquidator][
      params.collateralReserveId
    ];
    ISpoke.PositionStatus storage userPositionStatus = positionStatus[params.user];

    return
      _executeLiquidation({
        collateralUserPosition: collateralUserPosition,
        debtUserPosition: debtUserPosition,
        collateralLiquidatorPosition: collateralLiquidatorPosition,
        userPositionStatus: userPositionStatus,
        params: executeLiquidationParams
      });
  }

  /// @notice Reports deficits for all debt reserves of the user.
  /// @dev Deficit validation should already have occurred during liquidation.
  /// @dev It clears the user position, setting drawn debt, premium debt and user risk premium to zero.
  /// @param reserves The mapping of reserves per reserve identifier.
  /// @param userPositions The mapping of user positions per reserve per user.
  /// @param positionStatus The mapping of position status per user.
  /// @param reserveCount The number of reserves.
  /// @param user The address of the user.
  function notifyReportDeficit(
    mapping(uint256 reserveId => ISpoke.Reserve) storage reserves,
    mapping(address user => mapping(uint256 reserveId => ISpoke.UserPosition)) storage userPositions,
    mapping(address user => ISpoke.PositionStatus) storage positionStatus,
    uint256 reserveCount,
    address user
  ) external {
    ISpoke.PositionStatus storage userPositionStatus = positionStatus[user];
    userPositionStatus.riskPremium = 0;

    uint256 reserveId = reserveCount;
    while (
      (reserveId = userPositionStatus.nextBorrowing(reserveId)) != PositionStatusMap.NOT_FOUND
    ) {
      ISpoke.UserPosition storage userPosition = userPositions[user][reserveId];
      ISpoke.Reserve storage reserve = reserves[reserveId];
      IHubBase hub = reserve.hub;
      uint256 assetId = reserve.assetId;

      UserPositionUtils.DebtComponents memory debtComponents = userPosition.getDebtComponents(
        hub,
        assetId
      );
      IHubBase.PremiumDelta memory premiumDelta = userPosition.calculatePremiumDelta({
        drawnSharesTaken: debtComponents.drawnShares,
        drawnIndex: debtComponents.drawnIndex,
        riskPremium: 0,
        restoredPremiumRay: debtComponents.premiumDebtRay
      });

      hub.reportDeficit(
        assetId,
        debtComponents.drawnShares.rayMulUp(debtComponents.drawnIndex),
        premiumDelta
      );
      userPosition.applyPremiumDelta(premiumDelta);
      userPosition.drawnShares -= debtComponents.drawnShares.toUint120();
      userPositionStatus.setBorrowing(reserveId, false);

      emit ISpoke.ReportDeficit(reserveId, user, debtComponents.drawnShares, premiumDelta);
    }

    emit ISpoke.UpdateUserRiskPremium(user, 0);
  }

  /// @notice Calculates the liquidation bonus at a given health factor.
  /// @dev Liquidation Bonus is expressed as a BPS value greater than `PercentageMath.PERCENTAGE_FACTOR`.
  /// @param healthFactorForMaxBonus The health factor for max bonus, expressed in WAD.
  /// @param liquidationBonusFactor The liquidation bonus factor, expressed in BPS.
  /// @param healthFactor The health factor, expressed in WAD.
  /// @param maxLiquidationBonus The max liquidation bonus, expressed in BPS.
  /// @return The liquidation bonus, expressed in BPS.
  function calculateLiquidationBonus(
    uint256 healthFactorForMaxBonus,
    uint256 liquidationBonusFactor,
    uint256 healthFactor,
    uint256 maxLiquidationBonus
  ) public pure returns (uint256) {
    if (healthFactor <= healthFactorForMaxBonus) {
      return maxLiquidationBonus;
    }

    uint256 minLiquidationBonus = (maxLiquidationBonus - PercentageMath.PERCENTAGE_FACTOR)
      .percentMulDown(liquidationBonusFactor) + PercentageMath.PERCENTAGE_FACTOR;

    // linear interpolation between min and max
    // denominator cannot be zero as healthFactorForMaxBonus is always < HEALTH_FACTOR_LIQUIDATION_THRESHOLD
    return
      minLiquidationBonus +
      (maxLiquidationBonus - minLiquidationBonus).mulDivDown(
        HEALTH_FACTOR_LIQUIDATION_THRESHOLD - healthFactor,
        HEALTH_FACTOR_LIQUIDATION_THRESHOLD - healthFactorForMaxBonus
      );
  }

  /// @dev Executes the liquidation.
  /// @param collateralUserPosition User's collateral position.
  /// @param debtUserPosition User's debt position.
  /// @param collateralLiquidatorPosition Liquidator's collateral position.
  /// @param userPositionStatus User's position status.
  /// @param params The execute liquidation params.
  /// @return True if the liquidation results in deficit.
  function _executeLiquidation(
    ISpoke.UserPosition storage collateralUserPosition,
    ISpoke.UserPosition storage debtUserPosition,
    ISpoke.UserPosition storage collateralLiquidatorPosition,
    ISpoke.PositionStatus storage userPositionStatus,
    ExecuteLiquidationParams memory params
  ) internal returns (bool) {
    uint256 suppliedShares = collateralUserPosition.suppliedShares;
    UserPositionUtils.DebtComponents memory debtComponents = debtUserPosition.getDebtComponents(
      params.debtHub,
      params.debtAssetId
    );

    _validateLiquidationCall(
      ValidateLiquidationCallParams({
        user: params.user,
        liquidator: params.liquidator,
        collateralReserveFlags: params.collateralReserveFlags,
        debtReserveFlags: params.debtReserveFlags,
        suppliedShares: suppliedShares,
        drawnShares: debtComponents.drawnShares,
        debtToCover: params.debtToCover,
        collateralFactor: params.collateralDynConfig.collateralFactor,
        isUsingAsCollateral: userPositionStatus.isUsingAsCollateral(params.collateralReserveId),
        healthFactor: params.healthFactor,
        receiveShares: params.receiveShares
      })
    );

    LiquidationAmounts memory liquidationAmounts = _calculateLiquidationAmounts(
      CalculateLiquidationAmountsParams({
        collateralReserveHub: params.collateralHub,
        collateralReserveAssetId: params.collateralAssetId,
        suppliedShares: suppliedShares,
        collateralAssetDecimals: params.collateralAssetDecimals,
        collateralAssetPrice: IAaveOracle(params.oracle).getReservePrice(
          params.collateralReserveId
        ),
        drawnShares: debtComponents.drawnShares,
        premiumDebtRay: debtComponents.premiumDebtRay,
        drawnIndex: debtComponents.drawnIndex,
        totalDebtValueRay: params.totalDebtValueRay,
        debtAssetDecimals: params.debtAssetDecimals,
        debtAssetPrice: IAaveOracle(params.oracle).getReservePrice(params.debtReserveId),
        debtToCover: params.debtToCover,
        collateralFactor: params.collateralDynConfig.collateralFactor,
        healthFactorForMaxBonus: params.liquidationConfig.healthFactorForMaxBonus,
        liquidationBonusFactor: params.liquidationConfig.liquidationBonusFactor,
        maxLiquidationBonus: params.collateralDynConfig.maxLiquidationBonus,
        targetHealthFactor: params.liquidationConfig.targetHealthFactor,
        healthFactor: params.healthFactor,
        liquidationFee: params.collateralDynConfig.liquidationFee
      })
    );

    LiquidateCollateralResult memory liquidateCollateralResult = _liquidateCollateral(
      collateralUserPosition,
      collateralLiquidatorPosition,
      LiquidateCollateralParams({
        hub: params.collateralHub,
        assetId: params.collateralAssetId,
        sharesToLiquidate: liquidationAmounts.collateralSharesToLiquidate,
        sharesToLiquidator: liquidationAmounts.collateralSharesToLiquidator,
        liquidator: params.liquidator,
        receiveShares: params.receiveShares
      })
    );

    LiquidateDebtResult memory liquidateDebtResult = _liquidateDebt(
      debtUserPosition,
      userPositionStatus,
      LiquidateDebtParams({
        hub: params.debtHub,
        assetId: params.debtAssetId,
        underlying: params.debtUnderlying,
        reserveId: params.debtReserveId,
        drawnSharesToLiquidate: liquidationAmounts.drawnSharesToLiquidate,
        premiumDebtRayToLiquidate: liquidationAmounts.premiumDebtRayToLiquidate,
        drawnIndex: debtComponents.drawnIndex,
        liquidator: params.liquidator
      })
    );

    emit ISpoke.LiquidationCall({
      collateralReserveId: params.collateralReserveId,
      debtReserveId: params.debtReserveId,
      user: params.user,
      liquidator: params.liquidator,
      receiveShares: params.receiveShares,
      debtAmountRestored: liquidateDebtResult.amountRestored,
      drawnSharesLiquidated: liquidationAmounts.drawnSharesToLiquidate,
      premiumDelta: liquidateDebtResult.premiumDelta,
      collateralAmountRemoved: liquidateCollateralResult.amountRemoved,
      collateralSharesLiquidated: liquidationAmounts.collateralSharesToLiquidate,
      collateralSharesToLiquidator: liquidationAmounts.collateralSharesToLiquidator
    });

    return
      _evaluateDeficit({
        isCollateralPositionEmpty: liquidateCollateralResult.isCollateralPositionEmpty,
        isDebtPositionEmpty: liquidateDebtResult.isDebtPositionEmpty,
        activeCollateralCount: params.activeCollateralCount,
        borrowCount: params.borrowCount
      });
  }

  /// @dev Invoked by `liquidateUser` method.
  /// @return The liquidate collateral result.
  function _liquidateCollateral(
    ISpoke.UserPosition storage userPosition,
    ISpoke.UserPosition storage liquidatorPosition,
    LiquidateCollateralParams memory params
  ) internal returns (LiquidateCollateralResult memory) {
    uint120 newUserSuppliedShares = userPosition.suppliedShares -
      params.sharesToLiquidate.toUint120();
    userPosition.suppliedShares = newUserSuppliedShares;

    uint256 amountRemoved = params.hub.previewRemoveByShares(
      params.assetId,
      params.sharesToLiquidate
    );

    if (params.sharesToLiquidator > 0) {
      if (params.receiveShares) {
        liquidatorPosition.suppliedShares += params.sharesToLiquidator.toUint120();
      } else {
        uint256 amountToLiquidator = amountRemoved;
        if (params.sharesToLiquidator < params.sharesToLiquidate) {
          amountToLiquidator = params.hub.previewRemoveByShares(
            params.assetId,
            params.sharesToLiquidator
          );
        }
        params.hub.remove(params.assetId, amountToLiquidator, params.liquidator);
      }
    }

    uint256 feeShares = params.sharesToLiquidate - params.sharesToLiquidator;
    if (feeShares > 0) {
      params.hub.payFeeShares(params.assetId, feeShares);
    }

    return
      LiquidateCollateralResult({
        amountRemoved: amountRemoved,
        isCollateralPositionEmpty: newUserSuppliedShares == 0
      });
  }

  /// @dev Invoked by `liquidateUser` method.
  /// @return The liquidate debt result.
  function _liquidateDebt(
    ISpoke.UserPosition storage userPosition,
    ISpoke.PositionStatus storage positionStatus,
    LiquidateDebtParams memory params
  ) internal returns (LiquidateDebtResult memory) {
    IHubBase.PremiumDelta memory premiumDelta = userPosition.calculatePremiumDelta({
      drawnSharesTaken: params.drawnSharesToLiquidate,
      drawnIndex: params.drawnIndex,
      riskPremium: positionStatus.riskPremium,
      restoredPremiumRay: params.premiumDebtRayToLiquidate
    });

    uint256 drawnAmountToRestore = params.drawnSharesToLiquidate.rayMulUp(params.drawnIndex);
    uint256 amountToRestore = drawnAmountToRestore + params.premiumDebtRayToLiquidate.fromRayUp();
    IERC20(params.underlying).safeTransferFrom(
      params.liquidator,
      address(params.hub),
      amountToRestore
    );
    params.hub.restore(params.assetId, drawnAmountToRestore, premiumDelta);

    userPosition.applyPremiumDelta(premiumDelta);
    userPosition.drawnShares -= params.drawnSharesToLiquidate.toUint120();

    bool isDebtPositionEmpty;
    if (userPosition.drawnShares == 0) {
      positionStatus.setBorrowing(params.reserveId, false);
      isDebtPositionEmpty = true;
    }

    return
      LiquidateDebtResult({
        amountRestored: amountToRestore,
        premiumDelta: premiumDelta,
        isDebtPositionEmpty: isDebtPositionEmpty
      });
  }

  /// @notice Validates the liquidation call.
  /// @param params The validate liquidation call params.
  function _validateLiquidationCall(ValidateLiquidationCallParams memory params) internal pure {
    require(params.user != params.liquidator, ISpoke.SelfLiquidation());
    require(params.debtToCover > 0, ISpoke.InvalidDebtToCover());
    require(
      !params.collateralReserveFlags.paused() && !params.debtReserveFlags.paused(),
      ISpoke.ReservePaused()
    );
    require(params.suppliedShares > 0, ISpoke.ReserveNotSupplied());
    // user has active debt if and only if user has drawn shares (premium debt is always repaid first,
    // and can only be created when drawn shares exist)
    require(params.drawnShares > 0, ISpoke.ReserveNotBorrowed());
    require(
      params.healthFactor < HEALTH_FACTOR_LIQUIDATION_THRESHOLD,
      ISpoke.HealthFactorNotBelowThreshold()
    );
    require(
      params.collateralFactor > 0 && params.isUsingAsCollateral,
      ISpoke.ReserveNotEnabledAsCollateral()
    );
    if (params.receiveShares) {
      require(
        !params.collateralReserveFlags.frozen() &&
          params.collateralReserveFlags.receiveSharesEnabled(),
        ISpoke.CannotReceiveShares()
      );
    }
  }

  /// @notice Calculates the liquidation amounts.
  /// @dev Invoked by `liquidateUser` method.
  function _calculateLiquidationAmounts(
    CalculateLiquidationAmountsParams memory params
  ) internal view returns (LiquidationAmounts memory) {
    uint256 collateralAssetUnit = MathUtils.uncheckedExp(10, params.collateralAssetDecimals);
    uint256 debtAssetUnit = MathUtils.uncheckedExp(10, params.debtAssetDecimals);

    uint256 liquidationBonus = calculateLiquidationBonus({
      healthFactorForMaxBonus: params.healthFactorForMaxBonus,
      liquidationBonusFactor: params.liquidationBonusFactor,
      healthFactor: params.healthFactor,
      maxLiquidationBonus: params.maxLiquidationBonus
    });

    // To prevent accumulation of dust, one of the following conditions is enforced:
    // 1. liquidate all debt
    // 2. liquidate all collateral
    // 3. leave at least `DUST_LIQUIDATION_THRESHOLD` of collateral and debt (in value terms)
    (uint256 drawnSharesToLiquidate, uint256 premiumDebtRayToLiquidate) = _calculateDebtToLiquidate(
      CalculateDebtToLiquidateParams({
        drawnShares: params.drawnShares,
        premiumDebtRay: params.premiumDebtRay,
        drawnIndex: params.drawnIndex,
        totalDebtValueRay: params.totalDebtValueRay,
        debtAssetDecimals: params.debtAssetDecimals,
        debtAssetUnit: debtAssetUnit,
        debtAssetPrice: params.debtAssetPrice,
        debtToCover: params.debtToCover,
        collateralFactor: params.collateralFactor,
        liquidationBonus: liquidationBonus,
        healthFactor: params.healthFactor,
        targetHealthFactor: params.targetHealthFactor
      })
    );

    uint256 collateralSharesToLiquidate = _calculateCollateralToLiquidate(
      CalculateCollateralToLiquidateParams({
        collateralReserveHub: params.collateralReserveHub,
        collateralReserveAssetId: params.collateralReserveAssetId,
        collateralAssetUnit: collateralAssetUnit,
        collateralAssetPrice: params.collateralAssetPrice,
        drawnSharesToLiquidate: drawnSharesToLiquidate,
        premiumDebtRayToLiquidate: premiumDebtRayToLiquidate,
        drawnIndex: params.drawnIndex,
        debtAssetUnit: debtAssetUnit,
        debtAssetPrice: params.debtAssetPrice,
        liquidationBonus: liquidationBonus
      })
    );

    bool leavesCollateralDust;
    if (collateralSharesToLiquidate < params.suppliedShares) {
      uint256 collateralRemaining = params.collateralReserveHub.previewRemoveByShares(
        params.collateralReserveAssetId,
        params.suppliedShares.uncheckedSub(collateralSharesToLiquidate)
      );
      leavesCollateralDust =
        collateralRemaining.toValue({
          decimals: params.collateralAssetDecimals,
          price: params.collateralAssetPrice
        }) < DUST_LIQUIDATION_THRESHOLD;
    }

    // debt is fully liquidated if and only if all drawn shares are liquidated
    if (
      collateralSharesToLiquidate > params.suppliedShares ||
      (leavesCollateralDust && drawnSharesToLiquidate < params.drawnShares)
    ) {
      collateralSharesToLiquidate = params.suppliedShares;

      // - `debtRayToLiquidate` is decreased if `collateralSharesToLiquidate > params.suppliedShares` (if so, debt dust could remain).
      // - `debtRayToLiquidate` is increased if `(leavesCollateralDust && drawnSharesToLiquidate < params.drawnShares)`,
      // ensuring collateral reserve is fully liquidated (potentially bypassing the target health factor).
      uint256 debtRayToLiquidate = Math.mulDiv(
        params.collateralReserveHub.previewAddByShares(
          params.collateralReserveAssetId,
          collateralSharesToLiquidate
        ),
        params.collateralAssetPrice *
          debtAssetUnit *
          PercentageMath.PERCENTAGE_FACTOR *
          WadRayMath.RAY,
        params.debtAssetPrice * collateralAssetUnit * liquidationBonus,
        Math.Rounding.Ceil
      );

      if (debtRayToLiquidate <= params.premiumDebtRay) {
        // `premiumDebtRayToLiquidate` may exceed `debtRayToLiquidate` as a result of rounding up to asset units, ensuring full utilization of assets
        premiumDebtRayToLiquidate = debtRayToLiquidate.roundRayUp().min(params.premiumDebtRay);
        drawnSharesToLiquidate = 0;
      } else {
        premiumDebtRayToLiquidate = params.premiumDebtRay;
        drawnSharesToLiquidate = (debtRayToLiquidate - premiumDebtRayToLiquidate).divUp(
          params.drawnIndex
        );

        // `drawnSharesToLiquidate` may exceed `params.drawnShares` due to rounding.
        if (drawnSharesToLiquidate > params.drawnShares) {
          drawnSharesToLiquidate = params.drawnShares;

          // `collateralSharesToLiquidate` may exceed `params.suppliedShares` due to rounding.
          // If this happens, simply cap `collateralSharesToLiquidate` to `params.suppliedShares` since
          // debt to liquidate would be the same (it is already calculated based on `params.suppliedShares`).
          collateralSharesToLiquidate = _calculateCollateralToLiquidate(
            CalculateCollateralToLiquidateParams({
              collateralReserveHub: params.collateralReserveHub,
              collateralReserveAssetId: params.collateralReserveAssetId,
              collateralAssetUnit: collateralAssetUnit,
              collateralAssetPrice: params.collateralAssetPrice,
              drawnSharesToLiquidate: drawnSharesToLiquidate,
              premiumDebtRayToLiquidate: premiumDebtRayToLiquidate,
              drawnIndex: params.drawnIndex,
              debtAssetUnit: debtAssetUnit,
              debtAssetPrice: params.debtAssetPrice,
              liquidationBonus: liquidationBonus
            })
          ).min(params.suppliedShares);
        }
      }
    }

    // revert if the liquidator does not intend to cover the necessary debt to prevent dust from remaining
    require(
      params.debtToCover >=
        drawnSharesToLiquidate.rayMulUp(params.drawnIndex) + premiumDebtRayToLiquidate.fromRayUp(),
      ISpoke.MustNotLeaveDust()
    );

    uint256 collateralSharesToLiquidator = collateralSharesToLiquidate -
      collateralSharesToLiquidate.mulDivUp(
        params.liquidationFee * (liquidationBonus - PercentageMath.PERCENTAGE_FACTOR),
        liquidationBonus * PercentageMath.PERCENTAGE_FACTOR
      );

    return
      LiquidationAmounts({
        collateralSharesToLiquidate: collateralSharesToLiquidate,
        collateralSharesToLiquidator: collateralSharesToLiquidator,
        drawnSharesToLiquidate: drawnSharesToLiquidate,
        premiumDebtRayToLiquidate: premiumDebtRayToLiquidate
      });
  }

  /// @notice Calculates the amount of collateral shares that should be liquidated based on liquidated debt.
  /// @return The amount of collateral shares that should be liquidated.
  function _calculateCollateralToLiquidate(
    CalculateCollateralToLiquidateParams memory params
  ) internal view returns (uint256) {
    uint256 debtRayToLiquidate = params.drawnSharesToLiquidate * params.drawnIndex +
      params.premiumDebtRayToLiquidate;

    uint256 collateralToLiquidate = Math.mulDiv(
      debtRayToLiquidate,
      params.debtAssetPrice * params.collateralAssetUnit * params.liquidationBonus,
      params.debtAssetUnit *
        params.collateralAssetPrice *
        PercentageMath.PERCENTAGE_FACTOR *
        WadRayMath.RAY,
      Math.Rounding.Floor
    );

    uint256 collateralSharesToLiquidate = params.collateralReserveHub.previewAddByAssets(
      params.collateralReserveAssetId,
      collateralToLiquidate
    );

    return collateralSharesToLiquidate;
  }

  /// @notice Calculates the amount of drawn shares and premium debt that should be liquidated.
  /// @dev Returned values do not exceed `params.debtToCover`, except when all debt must be repaid due to remaining dust.
  /// @return The amount of drawn shares to liquidate. Does not exceed `params.drawnShares`.
  /// @return The amount of premium debt to liquidate. Does not exceed `params.premiumDebtRay`.
  function _calculateDebtToLiquidate(
    CalculateDebtToLiquidateParams memory params
  ) internal pure returns (uint256, uint256) {
    uint256 debtRayToTarget = _calculateDebtToTargetHealthFactor(
      CalculateDebtToTargetHealthFactorParams({
        totalDebtValueRay: params.totalDebtValueRay,
        debtAssetUnit: params.debtAssetUnit,
        debtAssetPrice: params.debtAssetPrice,
        collateralFactor: params.collateralFactor,
        liquidationBonus: params.liquidationBonus,
        healthFactor: params.healthFactor,
        targetHealthFactor: params.targetHealthFactor
      })
    );

    // `premiumDebtRayToLiquidate` may exceed `debtRayToTarget` as a result of rounding up to asset units, ensuring full utilization of assets
    uint256 premiumDebtRayToLiquidate = debtRayToTarget.roundRayUp().min(params.premiumDebtRay);
    // strict inequality is mandatory given rounding
    if (params.debtToCover < premiumDebtRayToLiquidate.fromRayUp()) {
      premiumDebtRayToLiquidate = params.debtToCover.toRay();
    }

    uint256 drawnSharesToLiquidate;
    if (
      premiumDebtRayToLiquidate == params.premiumDebtRay &&
      premiumDebtRayToLiquidate < debtRayToTarget
    ) {
      uint256 drawnSharesToTarget = (debtRayToTarget - premiumDebtRayToLiquidate).divUp(
        params.drawnIndex
      );
      uint256 drawnSharesToCover = Math.mulDiv(
        params.debtToCover - premiumDebtRayToLiquidate.fromRayUp(),
        WadRayMath.RAY,
        params.drawnIndex,
        Math.Rounding.Floor
      );

      drawnSharesToLiquidate = drawnSharesToTarget.min(drawnSharesToCover).min(params.drawnShares);
    }

    uint256 debtRayRemaining = (params.drawnShares - drawnSharesToLiquidate) * params.drawnIndex +
      params.premiumDebtRay -
      premiumDebtRayToLiquidate;

    // debt is fully liquidated if and only if all drawn shares are liquidated (premium debt is always liquidated first)
    bool leavesDebtDust = (drawnSharesToLiquidate < params.drawnShares) &&
      debtRayRemaining.toValue({decimals: params.debtAssetDecimals, price: params.debtAssetPrice}) <
        DUST_LIQUIDATION_THRESHOLD.toRay();

    if (leavesDebtDust) {
      // target health factor is bypassed to prevent leaving dust
      drawnSharesToLiquidate = params.drawnShares;
      premiumDebtRayToLiquidate = params.premiumDebtRay;
    }

    return (drawnSharesToLiquidate, premiumDebtRayToLiquidate);
  }

  /// @notice Calculates the amount of debt needed to be liquidated to restore a position to the target health factor.
  /// @return The amount of debt needed to be liquidated to restore user to the target health factor, expressed in units of debt asset and scaled by RAY.
  function _calculateDebtToTargetHealthFactor(
    CalculateDebtToTargetHealthFactorParams memory params
  ) internal pure returns (uint256) {
    // rounding direction has no effect on the result, as there is no precision loss in this calculation.
    uint256 liquidationPenalty = params.liquidationBonus.bpsToWad().percentMulUp(
      params.collateralFactor
    );

    // denominator cannot be zero as `liquidationPenalty` is always < PercentageMath.PERCENTAGE_FACTOR
    // `liquidationBonus.percentMulUp(collateralFactor) < PercentageMath.PERCENTAGE_FACTOR` is enforced in `_validateDynamicReserveConfig`
    // and targetHealthFactor is always >= HEALTH_FACTOR_LIQUIDATION_THRESHOLD
    return
      Math.mulDiv(
        params.totalDebtValueRay,
        params.debtAssetUnit * (params.targetHealthFactor - params.healthFactor),
        (params.targetHealthFactor - liquidationPenalty) * params.debtAssetPrice.toWad(),
        Math.Rounding.Ceil
      );
  }

  /// @notice Returns if the liquidation results in deficit.
  function _evaluateDeficit(
    bool isCollateralPositionEmpty,
    bool isDebtPositionEmpty,
    uint256 activeCollateralCount,
    uint256 borrowCount
  ) internal pure returns (bool) {
    if (!isCollateralPositionEmpty || activeCollateralCount > 1) {
      return false;
    }
    return !isDebtPositionEmpty || borrowCount > 1;
  }
}

// bench/LiquidationLogic.sol

contract PreviewHub {
  uint256 private constant TOTAL_ASSETS_WITH_VIRTUAL = 12_501.25e6;
  uint256 private constant TOTAL_SHARES_WITH_VIRTUAL = 10_001e6;

  function previewAddByAssets(uint256, uint256 assets) external pure returns (uint256) {
    return assets * TOTAL_SHARES_WITH_VIRTUAL / TOTAL_ASSETS_WITH_VIRTUAL;
  }

  function previewAddByShares(uint256, uint256 shares) external pure returns (uint256) {
    return
      (shares * TOTAL_ASSETS_WITH_VIRTUAL + TOTAL_SHARES_WITH_VIRTUAL - 1) /
      TOTAL_SHARES_WITH_VIRTUAL;
  }

  function previewRemoveByShares(uint256, uint256 shares) external pure returns (uint256) {
    return shares * TOTAL_ASSETS_WITH_VIRTUAL / TOTAL_SHARES_WITH_VIRTUAL;
  }
}

contract AGasTest {
  IHubBase private immutable collateralHub;

  constructor() {
    collateralHub = IHubBase(address(new PreviewHub()));
  }

  function liquidationAmountsEnoughCollateral()
    external
    view
    returns (LiquidationLogic.LiquidationAmounts memory)
  {
    return LiquidationLogic._calculateLiquidationAmounts(_amountParams(10_000e6));
  }

  function liquidationAmountsInsufficientCollateral()
    external
    view
    returns (LiquidationLogic.LiquidationAmounts memory)
  {
    return LiquidationLogic._calculateLiquidationAmounts(_amountParams(4500e6));
  }

  function _amountParams(uint256 suppliedShares)
    internal
    view
    returns (LiquidationLogic.CalculateLiquidationAmountsParams memory)
  {
    // Exact deterministic vector from
    // LiquidationLogic.LiquidationAmounts.t.sol.
    return LiquidationLogic.CalculateLiquidationAmountsParams({
      collateralReserveHub: collateralHub,
      collateralReserveAssetId: 0,
      suppliedShares: suppliedShares,
      collateralAssetDecimals: 6,
      collateralAssetPrice: 1e8,
      drawnShares: 3e18,
      premiumDebtRay: 0.5e18 * 1e27,
      drawnIndex: 1.6e27,
      totalDebtValueRay: 10_000e26 * 1e27,
      debtAssetDecimals: 18,
      debtAssetPrice: 2000e8,
      debtToCover: 3e18,
      collateralFactor: 50_00,
      healthFactorForMaxBonus: 0.8e18,
      liquidationBonusFactor: 50_00,
      maxLiquidationBonus: 120_00,
      targetHealthFactor: 1e18,
      healthFactor: 0.8e18,
      liquidationFee: 10_00
    });
  }

  function collateralToLiquidate()
    external
    view
    returns (uint256)
  {
    // Exact deterministic vector from
    // LiquidationLogic.CollateralToLiquidate.t.sol.
    return LiquidationLogic._calculateCollateralToLiquidate(
      LiquidationLogic.CalculateCollateralToLiquidateParams({
        collateralReserveHub: collateralHub,
        collateralReserveAssetId: 0,
        collateralAssetUnit: 1e6,
        collateralAssetPrice: 0.98e8,
        drawnSharesToLiquidate: 3e18,
        premiumDebtRayToLiquidate: 0.4e18 * 1e27,
        drawnIndex: 1.5e27,
        debtAssetUnit: 1e18,
        debtAssetPrice: 1000e8,
        liquidationBonus: 105_00
      })
    );
  }

  function debtToTargetHealthFactor(uint256 assetUnit)
    external
    pure
    returns (uint256)
  {
    // Upstream exercises asset units 1, 1e6 and 1e18 with this vector.
    return LiquidationLogic._calculateDebtToTargetHealthFactor(
      LiquidationLogic.CalculateDebtToTargetHealthFactorParams({
        totalDebtValueRay: 10_000e26 * 1e27,
        debtAssetPrice: 333e8,
        debtAssetUnit: assetUnit,
        collateralFactor: 50_00,
        liquidationBonus: 150_00,
        healthFactor: 0.8e18,
        targetHealthFactor: 1e18
      })
    );
  }

  function liquidationBonusPartial() external pure returns (uint256) {
    return LiquidationLogic.calculateLiquidationBonus({
      healthFactorForMaxBonus: 0.8e18,
      liquidationBonusFactor: 50_00,
      healthFactor: 0.96e18,
      maxLiquidationBonus: 110_00
    });
  }

  function liquidationBonusMax() external pure returns (uint256) {
    return LiquidationLogic.calculateLiquidationBonus({
      healthFactorForMaxBonus: 0.8e18,
      liquidationBonusFactor: 50_00,
      healthFactor: 0.8e18,
      maxLiquidationBonus: 110_00
    });
  }
}

// ----
// liquidationAmountsEnoughCollateral() -> 4800000000, 4720000000, 1250000000000000000, 500000000000000000000000000000000000000000000
// liquidationAmountsInsufficientCollateral() -> 4500000000, 4425000000, 1152343750000000000, 500000000000000000000000000000000000000000000
// collateralToLiquidate() -> 4200000000
// debtToTargetHealthFactor(uint256): 1 -> 24024024024024024024024024025
// debtToTargetHealthFactor(uint256): 1000000 -> 24024024024024024024024024024024025
// debtToTargetHealthFactor(uint256): 1000000000000000000 -> 24024024024024024024024024024024024024024024025
// liquidationBonusPartial() -> 10600
// liquidationBonusMax() -> 11000
