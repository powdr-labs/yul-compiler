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

// bench/PositionStatusMap.sol

contract AGasTest {
  using PositionStatusMap for ISpoke.PositionStatus;

  ISpoke.PositionStatus private collateralStatus;
  ISpoke.PositionStatus private borrowStatus;

  function configureCollateralCountVector() external {
    // Exact reserve ids and state transitions from test_collateralCount.
    collateralStatus.setUsingAsCollateral(127, true);
    collateralStatus.setUsingAsCollateral(128, true);
    collateralStatus.setUsingAsCollateral(2, true);
    collateralStatus.setUsingAsCollateral(32, true);
    collateralStatus.setUsingAsCollateral(342, true);
    collateralStatus.setUsingAsCollateral(32, false);
    collateralStatus.setBorrowing(32, true);
    collateralStatus.setBorrowing(79, true);
    collateralStatus.setBorrowing(255, true);
  }

  function collateralCount343() external view returns (uint256) {
    return collateralStatus.collateralCount(343);
  }

  function scanCollateralVector() external view returns (uint256 count) {
    uint256 reserveId = 343;
    while (true) {
      (reserveId, , ) = collateralStatus.next(reserveId);
      if (reserveId == type(uint256).max) return count;
      ++count;
    }
  }

  function configureBorrowCountVector() external {
    // Exact reserve ids and state transitions from test_borrowCount.
    borrowStatus.setBorrowing(127, true);
    borrowStatus.setBorrowing(128, true);
    borrowStatus.setBorrowing(2, true);
    borrowStatus.setBorrowing(32, true);
    borrowStatus.setBorrowing(342, true);
    borrowStatus.setBorrowing(32, false);
    borrowStatus.setUsingAsCollateral(32, true);
    borrowStatus.setUsingAsCollateral(79, true);
    borrowStatus.setUsingAsCollateral(255, true);
  }

  function borrowCount343() external view returns (uint256) {
    return borrowStatus.borrowCount(343);
  }

  function scanBorrowVector() external view returns (uint256 count) {
    uint256 reserveId = 343;
    while (true) {
      reserveId = borrowStatus.nextBorrowing(reserveId);
      if (reserveId == type(uint256).max) return count;
      ++count;
    }
  }
}

// ----
// configureCollateralCountVector() -> 0
// collateralCount343() -> 4
// scanCollateralVector() -> 7
// configureBorrowCountVector() -> 0
// borrowCount343() -> 4
// scanBorrowVector() -> 4
