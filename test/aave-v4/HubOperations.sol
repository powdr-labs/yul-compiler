// SPDX-License-Identifier: LicenseRef-BUSL
pragma solidity ^0.8.28;

// Aave v4 compiler/gas fixture for test environments only.
// Wrapper scenarios reproduce upstream tests; production sources are flattened
// from commit cfdf931c8c61715bef590c087c1fabe64c92ac92. See LICENSE.

// src/dependencies/openzeppelin/Comparators.sol

// OpenZeppelin Contracts (last updated v5.1.0) (utils/Comparators.sol)

/**
 * @dev Provides a set of functions to compare values.
 *
 * _Available since v5.1._
 */
library Comparators {
  function lt(uint256 a, uint256 b) internal pure returns (bool) {
    return a < b;
  }

  function gt(uint256 a, uint256 b) internal pure returns (bool) {
    return a > b;
  }
}

// src/dependencies/openzeppelin/Context.sol

// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
  function _msgSender() internal view virtual returns (address) {
    return msg.sender;
  }

  function _msgData() internal view virtual returns (bytes calldata) {
    return msg.data;
  }

  function _contextSuffixLength() internal view virtual returns (uint256) {
    return 0;
  }
}

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

// src/dependencies/openzeppelin/IAccessManager.sol

// OpenZeppelin Contracts (last updated v5.5.0) (access/manager/IAccessManager.sol)

interface IAccessManager {
  /**
   * @dev A delayed operation was scheduled.
   */
  event OperationScheduled(
    bytes32 indexed operationId,
    uint32 indexed nonce,
    uint48 schedule,
    address caller,
    address target,
    bytes data
  );

  /**
   * @dev A scheduled operation was executed.
   */
  event OperationExecuted(bytes32 indexed operationId, uint32 indexed nonce);

  /**
   * @dev A scheduled operation was canceled.
   */
  event OperationCanceled(bytes32 indexed operationId, uint32 indexed nonce);

  /**
   * @dev Informational labelling for a roleId.
   */
  event RoleLabel(uint64 indexed roleId, string label);

  /**
   * @dev Emitted when `account` is granted `roleId`.
   *
   * NOTE: The meaning of the `since` argument depends on the `newMember` argument.
   * If the role is granted to a new member, the `since` argument indicates when the account becomes a member of the role,
   * otherwise it indicates the execution delay for this account and roleId is updated.
   */
  event RoleGranted(
    uint64 indexed roleId,
    address indexed account,
    uint32 delay,
    uint48 since,
    bool newMember
  );

  /**
   * @dev Emitted when `account` membership or `roleId` is revoked. Unlike granting, revoking is instantaneous.
   */
  event RoleRevoked(uint64 indexed roleId, address indexed account);

  /**
   * @dev Role acting as admin over a given `roleId` is updated.
   */
  event RoleAdminChanged(uint64 indexed roleId, uint64 indexed admin);

  /**
   * @dev Role acting as guardian over a given `roleId` is updated.
   */
  event RoleGuardianChanged(uint64 indexed roleId, uint64 indexed guardian);

  /**
   * @dev Grant delay for a given `roleId` will be updated to `delay` when `since` is reached.
   */
  event RoleGrantDelayChanged(uint64 indexed roleId, uint32 delay, uint48 since);

  /**
   * @dev Target mode is updated (true = closed, false = open).
   */
  event TargetClosed(address indexed target, bool closed);

  /**
   * @dev Role required to invoke `selector` on `target` is updated to `roleId`.
   */
  event TargetFunctionRoleUpdated(address indexed target, bytes4 selector, uint64 indexed roleId);

  /**
   * @dev Admin delay for a given `target` will be updated to `delay` when `since` is reached.
   */
  event TargetAdminDelayUpdated(address indexed target, uint32 delay, uint48 since);

  error AccessManagerAlreadyScheduled(bytes32 operationId);
  error AccessManagerNotScheduled(bytes32 operationId);
  error AccessManagerNotReady(bytes32 operationId);
  error AccessManagerExpired(bytes32 operationId);
  error AccessManagerLockedRole(uint64 roleId);
  error AccessManagerBadConfirmation();
  error AccessManagerUnauthorizedAccount(address msgsender, uint64 roleId);
  error AccessManagerUnauthorizedCall(address caller, address target, bytes4 selector);
  error AccessManagerUnauthorizedConsume(address target);
  error AccessManagerUnauthorizedCancel(
    address msgsender,
    address caller,
    address target,
    bytes4 selector
  );
  error AccessManagerInvalidInitialAdmin(address initialAdmin);

  /**
   * @dev Check if an address (`caller`) is authorised to call a given function on a given contract directly (with
   * no restriction). Additionally, it returns the delay needed to perform the call indirectly through the {schedule}
   * & {execute} workflow.
   *
   * This function is usually called by the targeted contract to control immediate execution of restricted functions.
   * Therefore we only return true if the call can be performed without any delay. If the call is subject to a
   * previously set delay (not zero), then the function should return false and the caller should schedule the operation
   * for future execution.
   *
   * If `allowed` is true, the delay can be disregarded and the operation can be immediately executed, otherwise
   * the operation can be executed if and only if delay is greater than 0.
   *
   * NOTE: The IAuthority interface does not include the `uint32` delay. This is an extension of that interface that
   * is backward compatible. Some contracts may thus ignore the second return argument. In that case they will fail
   * to identify the indirect workflow, and will consider calls that require a delay to be forbidden.
   *
   * NOTE: This function does not report the permissions of the admin functions in the manager itself. These are defined by the
   * {AccessManager} documentation.
   */
  function canCall(
    address caller,
    address target,
    bytes4 selector
  ) external view returns (bool allowed, uint32 delay);

  /**
   * @dev Expiration delay for scheduled proposals. Defaults to 1 week.
   *
   * IMPORTANT: Avoid overriding the expiration with 0. Otherwise every contract proposal will be expired immediately,
   * disabling any scheduling usage.
   */
  function expiration() external view returns (uint32);

  /**
   * @dev Minimum setback for all delay updates, with the exception of execution delays. It
   * can be increased without setback (and reset via {revokeRole} in the event of an
   * accidental increase). Defaults to 5 days.
   */
  function minSetback() external view returns (uint32);

  /**
   * @dev Get whether the contract is closed disabling any access. Otherwise role permissions are applied.
   *
   * NOTE: When the manager itself is closed, admin functions are still accessible to avoid locking the contract.
   */
  function isTargetClosed(address target) external view returns (bool);

  /**
   * @dev Get the role required to call a function.
   */
  function getTargetFunctionRole(address target, bytes4 selector) external view returns (uint64);

  /**
   * @dev Get the admin delay for a target contract. Changes to contract configuration are subject to this delay.
   */
  function getTargetAdminDelay(address target) external view returns (uint32);

  /**
   * @dev Get the id of the role that acts as an admin for the given role.
   *
   * The admin permission is required to grant the role, revoke the role and update the execution delay to execute
   * an operation that is restricted to this role.
   */
  function getRoleAdmin(uint64 roleId) external view returns (uint64);

  /**
   * @dev Get the role that acts as a guardian for a given role.
   *
   * The guardian permission allows canceling operations that have been scheduled under the role.
   */
  function getRoleGuardian(uint64 roleId) external view returns (uint64);

  /**
   * @dev Get the role current grant delay.
   *
   * Its value may change at any point without an event emitted following a call to {setGrantDelay}.
   * Changes to this value, including effect timepoint are notified in advance by the {RoleGrantDelayChanged} event.
   */
  function getRoleGrantDelay(uint64 roleId) external view returns (uint32);

  /**
   * @dev Get the access details for a given account for a given role. These details include the timepoint at which
   * membership becomes active, and the delay applied to all operations by this user that requires this permission
   * level.
   *
   * Returns:
   * [0] Timestamp at which the account membership becomes valid. 0 means role is not granted.
   * [1] Current execution delay for the account.
   * [2] Pending execution delay for the account.
   * [3] Timestamp at which the pending execution delay will become active. 0 means no delay update is scheduled.
   */
  function getAccess(
    uint64 roleId,
    address account
  ) external view returns (uint48 since, uint32 currentDelay, uint32 pendingDelay, uint48 effect);

  /**
   * @dev Check if a given account currently has the permission level corresponding to a given role. Note that this
   * permission might be associated with an execution delay. {getAccess} can provide more details.
   */
  function hasRole(
    uint64 roleId,
    address account
  ) external view returns (bool isMember, uint32 executionDelay);

  /**
   * @dev Give a label to a role, for improved role discoverability by UIs.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   *
   * Emits a {RoleLabel} event.
   */
  function labelRole(uint64 roleId, string calldata label) external;

  /**
   * @dev Add `account` to `roleId`, or change its execution delay.
   *
   * This gives the account the authorization to call any function that is restricted to this role. An optional
   * execution delay (in seconds) can be set. If that delay is non 0, the user is required to schedule any operation
   * that is restricted to members of this role. The user will only be able to execute the operation after the delay has
   * passed, before it has expired. During this period, admin and guardians can cancel the operation (see {cancel}).
   *
   * If the account has already been granted this role, the execution delay will be updated. This update is not
   * immediate and follows the delay rules. For example, if a user currently has a delay of 3 hours, and this is
   * called to reduce that delay to 1 hour, the new delay will take some time to take effect, enforcing that any
   * operation executed in the 3 hours that follows this update was indeed scheduled before this update.
   *
   * Requirements:
   *
   * - the caller must be an admin for the role (see {getRoleAdmin})
   * - granted role must not be the `PUBLIC_ROLE`
   *
   * Emits a {RoleGranted} event.
   */
  function grantRole(uint64 roleId, address account, uint32 executionDelay) external;

  /**
   * @dev Remove an account from a role, with immediate effect. If the account does not have the role, this call has
   * no effect.
   *
   * Requirements:
   *
   * - the caller must be an admin for the role (see {getRoleAdmin})
   * - revoked role must not be the `PUBLIC_ROLE`
   *
   * Emits a {RoleRevoked} event if the account had the role.
   */
  function revokeRole(uint64 roleId, address account) external;

  /**
   * @dev Renounce role permissions for the calling account with immediate effect. If the sender is not in
   * the role this call has no effect.
   *
   * Requirements:
   *
   * - the caller must be `callerConfirmation`.
   *
   * Emits a {RoleRevoked} event if the account had the role.
   */
  function renounceRole(uint64 roleId, address callerConfirmation) external;

  /**
   * @dev Change admin role for a given role.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   *
   * Emits a {RoleAdminChanged} event
   */
  function setRoleAdmin(uint64 roleId, uint64 admin) external;

  /**
   * @dev Change guardian role for a given role.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   *
   * Emits a {RoleGuardianChanged} event
   */
  function setRoleGuardian(uint64 roleId, uint64 guardian) external;

  /**
   * @dev Update the delay for granting a `roleId`.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   *
   * Emits a {RoleGrantDelayChanged} event.
   */
  function setGrantDelay(uint64 roleId, uint32 newDelay) external;

  /**
   * @dev Set the role required to call functions identified by the `selectors` in the `target` contract.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   *
   * Emits a {TargetFunctionRoleUpdated} event per selector.
   */
  function setTargetFunctionRole(
    address target,
    bytes4[] calldata selectors,
    uint64 roleId
  ) external;

  /**
   * @dev Set the delay for changing the configuration of a given target contract.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   *
   * Emits a {TargetAdminDelayUpdated} event.
   */
  function setTargetAdminDelay(address target, uint32 newDelay) external;

  /**
   * @dev Set the closed flag for a contract.
   *
   * Closing the manager itself won't disable access to admin methods to avoid locking the contract.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   *
   * Emits a {TargetClosed} event.
   */
  function setTargetClosed(address target, bool closed) external;

  /**
   * @dev Return the timepoint at which a scheduled operation will be ready for execution. This returns 0 if the
   * operation is not yet scheduled, has expired, was executed, or was canceled.
   */
  function getSchedule(bytes32 id) external view returns (uint48);

  /**
   * @dev Return the nonce for the latest scheduled operation with a given id. Returns 0 if the operation has never
   * been scheduled.
   */
  function getNonce(bytes32 id) external view returns (uint32);

  /**
   * @dev Schedule a delayed operation for future execution, and return the operation identifier. It is possible to
   * choose the timestamp at which the operation becomes executable as long as it satisfies the execution delays
   * required for the caller. The special value zero will automatically set the earliest possible time.
   *
   * Returns the `operationId` that was scheduled. Since this value is a hash of the parameters, it can reoccur when
   * the same parameters are used; if this is relevant, the returned `nonce` can be used to uniquely identify this
   * scheduled operation from other occurrences of the same `operationId` in invocations of {execute} and {cancel}.
   *
   * Emits a {OperationScheduled} event.
   *
   * NOTE: It is not possible to concurrently schedule more than one operation with the same `target` and `data`. If
   * this is necessary, a random byte can be appended to `data` to act as a salt that will be ignored by the target
   * contract if it is using standard Solidity ABI encoding.
   */
  function schedule(
    address target,
    bytes calldata data,
    uint48 when
  ) external returns (bytes32 operationId, uint32 nonce);

  /**
   * @dev Execute a function that is delay restricted, provided it was properly scheduled beforehand, or the
   * execution delay is 0.
   *
   * Returns the nonce that identifies the previously scheduled operation that is executed, or 0 if the
   * operation wasn't previously scheduled (if the caller doesn't have an execution delay).
   *
   * Emits an {OperationExecuted} event only if the call was scheduled and delayed.
   */
  function execute(address target, bytes calldata data) external payable returns (uint32);

  /**
   * @dev Cancel a scheduled (delayed) operation. Returns the nonce that identifies the previously scheduled
   * operation that is cancelled.
   *
   * Requirements:
   *
   * - the caller must be the proposer, a guardian of the targeted function, or a global admin
   *
   * Emits a {OperationCanceled} event.
   */
  function cancel(address caller, address target, bytes calldata data) external returns (uint32);

  /**
   * @dev Consume a scheduled operation targeting the caller. If such an operation exists, mark it as consumed
   * (emit an {OperationExecuted} event and clean the state). Otherwise, throw an error.
   *
   * This is useful for contracts that want to enforce that calls targeting them were scheduled on the manager,
   * with all the verifications that it implies.
   *
   * Emit a {OperationExecuted} event.
   */
  function consumeScheduledOp(address caller, bytes calldata data) external;

  /**
   * @dev Hashing function for delayed operations.
   */
  function hashOperation(
    address caller,
    address target,
    bytes calldata data
  ) external view returns (bytes32);

  /**
   * @dev Changes the authority of a target managed by this manager instance.
   *
   * Requirements:
   *
   * - the caller must be a global admin
   */
  function updateAuthority(address target, address newAuthority) external;
}

// src/dependencies/openzeppelin/IAuthority.sol

// OpenZeppelin Contracts (last updated v5.4.0) (access/manager/IAuthority.sol)

/**
 * @dev Standard interface for permissioning originally defined in Dappsys.
 */
interface IAuthority {
  /**
   * @dev Returns true if the caller can invoke on a target the function identified by a function selector.
   */
  function canCall(
    address caller,
    address target,
    bytes4 selector
  ) external view returns (bool allowed);
}

// src/hub/interfaces/IBasicInterestRateStrategy.sol

/// @title IBasicInterestRateStrategy
/// @author Aave Labs
/// @notice Basic interface for any interest rate strategy.
interface IBasicInterestRateStrategy {
  /// @notice Thrown when the interest rate data is not set for the asset.
  /// @param assetId The identifier of the asset with no interest rate data set.
  error InterestRateDataNotSet(uint256 assetId);

  /// @notice Sets the interest rate parameters for a specified asset.
  /// @param assetId The identifier of the asset.
  /// @param data The encoded parameters used to configure the interest rate of the asset.
  function setInterestRateData(uint256 assetId, bytes calldata data) external;

  /// @notice Calculates the interest rate depending on the asset's state and configurations.
  /// @param assetId The identifier of the asset.
  /// @param liquidity The current available liquidity of the asset.
  /// @param drawn The current drawn amount of the asset.
  /// @param deficit The current deficit of the asset.
  /// @param swept The current swept (reinvested) amount of the asset.
  /// @return The interest rate, expressed in RAY.
  function calculateInterestRate(
    uint256 assetId,
    uint256 liquidity,
    uint256 drawn,
    uint256 deficit,
    uint256 swept
  ) external view returns (uint256);
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

// src/dependencies/openzeppelin/IERC20Permit.sol

// OpenZeppelin Contracts (last updated v5.4.0) (token/ERC20/extensions/IERC20Permit.sol)

/**
 * @dev Interface of the ERC-20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[ERC-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC-20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 *
 * ==== Security Considerations
 *
 * There are two important considerations concerning the use of `permit`. The first is that a valid permit signature
 * expresses an allowance, and it should not be assumed to convey additional meaning. In particular, it should not be
 * considered as an intention to spend the allowance in any specific way. The second is that because permits have
 * built-in replay protection and can be submitted by anyone, they can be frontrun. A protocol that uses permits should
 * take this into consideration and allow a `permit` call to fail. Combining these two aspects, a pattern that may be
 * generally recommended is:
 *
 * ```solidity
 * function doThingWithPermit(..., uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) public {
 *     try token.permit(msg.sender, address(this), value, deadline, v, r, s) {} catch {}
 *     doThing(..., value);
 * }
 *
 * function doThing(..., uint256 value) public {
 *     token.safeTransferFrom(msg.sender, address(this), value);
 *     ...
 * }
 * ```
 *
 * Observe that: 1) `msg.sender` is used as the owner, leaving no ambiguity as to the signer intent, and 2) the use of
 * `try/catch` allows the permit to fail and makes the code tolerant to frontrunning. (See also
 * {SafeERC20-safeTransferFrom}).
 *
 * Additionally, note that smart contract wallets (such as Argent or Safe) are not able to produce permit signatures, so
 * contracts should have entry points that don't rely on permit.
 */
interface IERC20Permit {
  /**
   * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
   * given ``owner``'s signed approval.
   *
   * IMPORTANT: The same issues {IERC20-approve} has related to transaction
   * ordering also apply here.
   *
   * Emits an {Approval} event.
   *
   * Requirements:
   *
   * - `spender` cannot be the zero address.
   * - `deadline` must be a timestamp in the future.
   * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
   * over the EIP712-formatted function arguments.
   * - the signature must use ``owner``'s current nonce (see {nonces}).
   *
   * For more information on the signature format, see the
   * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
   * section].
   *
   * CAUTION: See Security Considerations above.
   */
  function permit(
    address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) external;

  /**
   * @dev Returns the current nonce for `owner`. This value must be
   * included whenever a signature is generated for {permit}.
   *
   * Every successful call to {permit} increases ``owner``'s nonce by one. This
   * prevents a signature from being used multiple times.
   */
  function nonces(address owner) external view returns (uint256);

  /**
   * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
   */
  // solhint-disable-next-line func-name-mixedcase
  function DOMAIN_SEPARATOR() external view returns (bytes32);
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

// src/dependencies/openzeppelin-upgradeable/Initializable.sol

// OpenZeppelin Contracts (last updated v5.3.0) (proxy/utils/Initializable.sol)

/**
 * @dev This is a base contract to aid in writing upgradeable contracts, or any kind of contract that will be deployed
 * behind a proxy. Since proxied contracts do not make use of a constructor, it's common to move constructor logic to an
 * external initializer function, usually called `initialize`. It then becomes necessary to protect this initializer
 * function so it can only be called once. The {initializer} modifier provided by this contract will have this effect.
 *
 * The initialization functions use a version number. Once a version number is used, it is consumed and cannot be
 * reused. This mechanism prevents re-execution of each "step" but allows the creation of new initialization steps in
 * case an upgrade adds a module that needs to be initialized.
 *
 * For example:
 *
 * [.hljs-theme-light.nopadding]
 * ```solidity
 * contract MyToken is ERC20Upgradeable {
 *     function initialize() initializer public {
 *         __ERC20_init("MyToken", "MTK");
 *     }
 * }
 *
 * contract MyTokenV2 is MyToken, ERC20PermitUpgradeable {
 *     function initializeV2() reinitializer(2) public {
 *         __ERC20Permit_init("MyToken");
 *     }
 * }
 * ```
 *
 * TIP: To avoid leaving the proxy in an uninitialized state, the initializer function should be called as early as
 * possible by providing the encoded function call as the `_data` argument to {ERC1967Proxy-constructor}.
 *
 * CAUTION: When used with inheritance, manual care must be taken to not invoke a parent initializer twice, or to ensure
 * that all initializers are idempotent. This is not verified automatically as constructors are by Solidity.
 *
 * [CAUTION]
 * ====
 * Avoid leaving a contract uninitialized.
 *
 * An uninitialized contract can be taken over by an attacker. This applies to both a proxy and its implementation
 * contract, which may impact the proxy. To prevent the implementation contract from being used, you should invoke
 * the {_disableInitializers} function in the constructor to automatically lock it when it is deployed:
 *
 * [.hljs-theme-light.nopadding]
 * ```
 * /// @custom:oz-upgrades-unsafe-allow constructor
 * constructor() {
 *     _disableInitializers();
 * }
 * ```
 * ====
 */
abstract contract Initializable {
  /**
   * @dev Storage of the initializable contract.
   *
   * It's implemented on a custom ERC-7201 namespace to reduce the risk of storage collisions
   * when using with upgradeable contracts.
   *
   * @custom:storage-location erc7201:openzeppelin.storage.Initializable
   */
  struct InitializableStorage {
    /**
     * @dev Indicates that the contract has been initialized.
     */
    uint64 _initialized;
    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool _initializing;
  }

  // keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.Initializable")) - 1)) & ~bytes32(uint256(0xff))
  bytes32 private constant INITIALIZABLE_STORAGE =
    0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00;

  /**
   * @dev The contract is already initialized.
   */
  error InvalidInitialization();

  /**
   * @dev The contract is not initializing.
   */
  error NotInitializing();

  /**
   * @dev Triggered when the contract has been initialized or reinitialized.
   */
  event Initialized(uint64 version);

  /**
   * @dev A modifier that defines a protected initializer function that can be invoked at most once. In its scope,
   * `onlyInitializing` functions can be used to initialize parent contracts.
   *
   * Similar to `reinitializer(1)`, except that in the context of a constructor an `initializer` may be invoked any
   * number of times. This behavior in the constructor can be useful during testing and is not expected to be used in
   * production.
   *
   * Emits an {Initialized} event.
   */
  modifier initializer() {
    // solhint-disable-next-line var-name-mixedcase
    InitializableStorage storage $ = _getInitializableStorage();

    // Cache values to avoid duplicated sloads
    bool isTopLevelCall = !$._initializing;
    uint64 initialized = $._initialized;

    // Allowed calls:
    // - initialSetup: the contract is not in the initializing state and no previous version was
    //                 initialized
    // - construction: the contract is initialized at version 1 (no reinitialization) and the
    //                 current contract is just being deployed
    bool initialSetup = initialized == 0 && isTopLevelCall;
    bool construction = initialized == 1 && address(this).code.length == 0;

    if (!initialSetup && !construction) {
      revert InvalidInitialization();
    }
    $._initialized = 1;
    if (isTopLevelCall) {
      $._initializing = true;
    }
    _;
    if (isTopLevelCall) {
      $._initializing = false;
      emit Initialized(1);
    }
  }

  /**
   * @dev A modifier that defines a protected reinitializer function that can be invoked at most once, and only if the
   * contract hasn't been initialized to a greater version before. In its scope, `onlyInitializing` functions can be
   * used to initialize parent contracts.
   *
   * A reinitializer may be used after the original initialization step. This is essential to configure modules that
   * are added through upgrades and that require initialization.
   *
   * When `version` is 1, this modifier is similar to `initializer`, except that functions marked with `reinitializer`
   * cannot be nested. If one is invoked in the context of another, execution will revert.
   *
   * Note that versions can jump in increments greater than 1; this implies that if multiple reinitializers coexist in
   * a contract, executing them in the right order is up to the developer or operator.
   *
   * WARNING: Setting the version to 2**64 - 1 will prevent any future reinitialization.
   *
   * Emits an {Initialized} event.
   */
  modifier reinitializer(uint64 version) {
    // solhint-disable-next-line var-name-mixedcase
    InitializableStorage storage $ = _getInitializableStorage();

    if ($._initializing || $._initialized >= version) {
      revert InvalidInitialization();
    }
    $._initialized = version;
    $._initializing = true;
    _;
    $._initializing = false;
    emit Initialized(version);
  }

  /**
   * @dev Modifier to protect an initialization function so that it can only be invoked by functions with the
   * {initializer} and {reinitializer} modifiers, directly or indirectly.
   */
  modifier onlyInitializing() {
    _checkInitializing();
    _;
  }

  /**
   * @dev Reverts if the contract is not in an initializing state. See {onlyInitializing}.
   */
  function _checkInitializing() internal view virtual {
    if (!_isInitializing()) {
      revert NotInitializing();
    }
  }

  /**
   * @dev Locks the contract, preventing any future reinitialization. This cannot be part of an initializer call.
   * Calling this in the constructor of a contract will prevent that contract from being initialized or reinitialized
   * to any version. It is recommended to use this to lock implementation contracts that are designed to be called
   * through proxies.
   *
   * Emits an {Initialized} event the first time it is successfully executed.
   */
  function _disableInitializers() internal virtual {
    // solhint-disable-next-line var-name-mixedcase
    InitializableStorage storage $ = _getInitializableStorage();

    if ($._initializing) {
      revert InvalidInitialization();
    }
    if ($._initialized != type(uint64).max) {
      $._initialized = type(uint64).max;
      emit Initialized(type(uint64).max);
    }
  }

  /**
   * @dev Returns the highest version that has been initialized. See {reinitializer}.
   */
  function _getInitializedVersion() internal view returns (uint64) {
    return _getInitializableStorage()._initialized;
  }

  /**
   * @dev Returns `true` if the contract is currently initializing. See {onlyInitializing}.
   */
  function _isInitializing() internal view returns (bool) {
    return _getInitializableStorage()._initializing;
  }

  /**
   * @dev Pointer to storage slot. Allows integrators to override it with a custom storage location.
   *
   * NOTE: Consider following the ERC-7201 formula to derive storage locations.
   */
  function _initializableStorageSlot() internal pure virtual returns (bytes32) {
    return INITIALIZABLE_STORAGE;
  }

  /**
   * @dev Returns a pointer to the storage namespace.
   */
  // solhint-disable-next-line var-name-mixedcase
  function _getInitializableStorage() private pure returns (InitializableStorage storage $) {
    bytes32 slot = _initializableStorageSlot();
    assembly {
      $.slot := slot
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

// src/dependencies/openzeppelin/SlotDerivation.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/SlotDerivation.sol)
// This file was procedurally generated from scripts/generate/templates/SlotDerivation.js.

/**
 * @dev Library for computing storage (and transient storage) locations from namespaces and deriving slots
 * corresponding to standard patterns. The derivation method for array and mapping matches the storage layout used by
 * the solidity language / compiler.
 *
 * See https://docs.soliditylang.org/en/v0.8.20/internals/layout_in_storage.html#mappings-and-dynamic-arrays[Solidity docs for mappings and dynamic arrays.].
 *
 * Example usage:
 * ```solidity
 * contract Example {
 *     // Add the library methods
 *     using StorageSlot for bytes32;
 *     using SlotDerivation for *;
 *
 *     // Declare a namespace
 *     string private constant _NAMESPACE = "<namespace>"; // eg. OpenZeppelin.Slot
 *
 *     function setValueInNamespace(uint256 key, address newValue) internal {
 *         _NAMESPACE.erc7201Slot().deriveMapping(key).getAddressSlot().value = newValue;
 *     }
 *
 *     function getValueInNamespace(uint256 key) internal view returns (address) {
 *         return _NAMESPACE.erc7201Slot().deriveMapping(key).getAddressSlot().value;
 *     }
 * }
 * ```
 *
 * TIP: Consider using this library along with {StorageSlot}.
 *
 * NOTE: This library provides a way to manipulate storage locations in a non-standard way. Tooling for checking
 * upgrade safety will ignore the slots accessed through this library.
 *
 * _Available since v5.1._
 */
library SlotDerivation {
  /**
   * @dev Derive an ERC-7201 slot from a string (namespace).
   */
  function erc7201Slot(string memory namespace) internal pure returns (bytes32 slot) {
    assembly ('memory-safe') {
      mstore(0x00, sub(keccak256(add(namespace, 0x20), mload(namespace)), 1))
      slot := and(keccak256(0x00, 0x20), not(0xff))
    }
  }

  /**
   * @dev Add an offset to a slot to get the n-th element of a structure or an array.
   */
  function offset(bytes32 slot, uint256 pos) internal pure returns (bytes32 result) {
    unchecked {
      return bytes32(uint256(slot) + pos);
    }
  }

  /**
   * @dev Derive the location of the first element in an array from the slot where the length is stored.
   */
  function deriveArray(bytes32 slot) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      mstore(0x00, slot)
      result := keccak256(0x00, 0x20)
    }
  }

  /**
   * @dev Derive the location of a mapping element from the key.
   */
  function deriveMapping(bytes32 slot, address key) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      mstore(0x00, and(key, shr(96, not(0))))
      mstore(0x20, slot)
      result := keccak256(0x00, 0x40)
    }
  }

  /**
   * @dev Derive the location of a mapping element from the key.
   */
  function deriveMapping(bytes32 slot, bool key) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      mstore(0x00, iszero(iszero(key)))
      mstore(0x20, slot)
      result := keccak256(0x00, 0x40)
    }
  }

  /**
   * @dev Derive the location of a mapping element from the key.
   */
  function deriveMapping(bytes32 slot, bytes32 key) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      mstore(0x00, key)
      mstore(0x20, slot)
      result := keccak256(0x00, 0x40)
    }
  }

  /**
   * @dev Derive the location of a mapping element from the key.
   */
  function deriveMapping(bytes32 slot, uint256 key) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      mstore(0x00, key)
      mstore(0x20, slot)
      result := keccak256(0x00, 0x40)
    }
  }

  /**
   * @dev Derive the location of a mapping element from the key.
   */
  function deriveMapping(bytes32 slot, int256 key) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      mstore(0x00, key)
      mstore(0x20, slot)
      result := keccak256(0x00, 0x40)
    }
  }

  /**
   * @dev Derive the location of a mapping element from the key.
   */
  function deriveMapping(bytes32 slot, string memory key) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      let length := mload(key)
      let begin := add(key, 0x20)
      let end := add(begin, length)
      let cache := mload(end)
      mstore(end, slot)
      result := keccak256(begin, add(length, 0x20))
      mstore(end, cache)
    }
  }

  /**
   * @dev Derive the location of a mapping element from the key.
   */
  function deriveMapping(bytes32 slot, bytes memory key) internal pure returns (bytes32 result) {
    assembly ('memory-safe') {
      let length := mload(key)
      let begin := add(key, 0x20)
      let end := add(begin, length)
      let cache := mload(end)
      mstore(end, slot)
      result := keccak256(begin, add(length, 0x20))
      mstore(end, cache)
    }
  }
}

// src/dependencies/openzeppelin/StorageSlot.sol

// OpenZeppelin Contracts (last updated v5.1.0) (utils/StorageSlot.sol)
// This file was procedurally generated from scripts/generate/templates/StorageSlot.js.

/**
 * @dev Library for reading and writing primitive types to specific storage slots.
 *
 * Storage slots are often used to avoid storage conflict when dealing with upgradeable contracts.
 * This library helps with reading and writing to such slots without the need for inline assembly.
 *
 * The functions in this library return Slot structs that contain a `value` member that can be used to read or write.
 *
 * Example usage to set ERC-1967 implementation slot:
 * ```solidity
 * contract ERC1967 {
 *     // Define the slot. Alternatively, use the SlotDerivation library to derive the slot.
 *     bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
 *
 *     function _getImplementation() internal view returns (address) {
 *         return StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value;
 *     }
 *
 *     function _setImplementation(address newImplementation) internal {
 *         require(newImplementation.code.length > 0);
 *         StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value = newImplementation;
 *     }
 * }
 * ```
 *
 * TIP: Consider using this library along with {SlotDerivation}.
 */
library StorageSlot {
  struct AddressSlot {
    address value;
  }

  struct BooleanSlot {
    bool value;
  }

  struct Bytes32Slot {
    bytes32 value;
  }

  struct Uint256Slot {
    uint256 value;
  }

  struct Int256Slot {
    int256 value;
  }

  struct StringSlot {
    string value;
  }

  struct BytesSlot {
    bytes value;
  }

  /**
   * @dev Returns an `AddressSlot` with member `value` located at `slot`.
   */
  function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
    assembly ('memory-safe') {
      r.slot := slot
    }
  }

  /**
   * @dev Returns a `BooleanSlot` with member `value` located at `slot`.
   */
  function getBooleanSlot(bytes32 slot) internal pure returns (BooleanSlot storage r) {
    assembly ('memory-safe') {
      r.slot := slot
    }
  }

  /**
   * @dev Returns a `Bytes32Slot` with member `value` located at `slot`.
   */
  function getBytes32Slot(bytes32 slot) internal pure returns (Bytes32Slot storage r) {
    assembly ('memory-safe') {
      r.slot := slot
    }
  }

  /**
   * @dev Returns a `Uint256Slot` with member `value` located at `slot`.
   */
  function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
    assembly ('memory-safe') {
      r.slot := slot
    }
  }

  /**
   * @dev Returns a `Int256Slot` with member `value` located at `slot`.
   */
  function getInt256Slot(bytes32 slot) internal pure returns (Int256Slot storage r) {
    assembly ('memory-safe') {
      r.slot := slot
    }
  }

  /**
   * @dev Returns a `StringSlot` with member `value` located at `slot`.
   */
  function getStringSlot(bytes32 slot) internal pure returns (StringSlot storage r) {
    assembly ('memory-safe') {
      r.slot := slot
    }
  }

  /**
   * @dev Returns an `StringSlot` representation of the string storage pointer `store`.
   */
  function getStringSlot(string storage store) internal pure returns (StringSlot storage r) {
    assembly ('memory-safe') {
      r.slot := store.slot
    }
  }

  /**
   * @dev Returns a `BytesSlot` with member `value` located at `slot`.
   */
  function getBytesSlot(bytes32 slot) internal pure returns (BytesSlot storage r) {
    assembly ('memory-safe') {
      r.slot := slot
    }
  }

  /**
   * @dev Returns an `BytesSlot` representation of the bytes storage pointer `store`.
   */
  function getBytesSlot(bytes storage store) internal pure returns (BytesSlot storage r) {
    assembly ('memory-safe') {
      r.slot := store.slot
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

// src/dependencies/openzeppelin/draft-IERC6093.sol

// OpenZeppelin Contracts (last updated v5.5.0) (interfaces/draft-IERC6093.sol)

/**
 * @dev Standard ERC-20 Errors
 * Interface of the https://eips.ethereum.org/EIPS/eip-6093[ERC-6093] custom errors for ERC-20 tokens.
 */
interface IERC20Errors {
  /**
   * @dev Indicates an error related to the current `balance` of a `sender`. Used in transfers.
   * @param sender Address whose tokens are being transferred.
   * @param balance Current balance for the interacting account.
   * @param needed Minimum amount required to perform a transfer.
   */
  error ERC20InsufficientBalance(address sender, uint256 balance, uint256 needed);

  /**
   * @dev Indicates a failure with the token `sender`. Used in transfers.
   * @param sender Address whose tokens are being transferred.
   */
  error ERC20InvalidSender(address sender);

  /**
   * @dev Indicates a failure with the token `receiver`. Used in transfers.
   * @param receiver Address to which tokens are being transferred.
   */
  error ERC20InvalidReceiver(address receiver);

  /**
   * @dev Indicates a failure with the `spender`’s `allowance`. Used in transfers.
   * @param spender Address that may be allowed to operate on tokens without being their owner.
   * @param allowance Amount of tokens a `spender` is allowed to operate with.
   * @param needed Minimum amount required to perform a transfer.
   */
  error ERC20InsufficientAllowance(address spender, uint256 allowance, uint256 needed);

  /**
   * @dev Indicates a failure with the `approver` of a token to be approved. Used in approvals.
   * @param approver Address initiating an approval operation.
   */
  error ERC20InvalidApprover(address approver);

  /**
   * @dev Indicates a failure with the `spender` to be approved. Used in approvals.
   * @param spender Address that may be allowed to operate on tokens without being their owner.
   */
  error ERC20InvalidSpender(address spender);
}

/**
 * @dev Standard ERC-721 Errors
 * Interface of the https://eips.ethereum.org/EIPS/eip-6093[ERC-6093] custom errors for ERC-721 tokens.
 */
interface IERC721Errors {
  /**
   * @dev Indicates that an address can't be an owner. For example, `address(0)` is a forbidden owner in ERC-721.
   * Used in balance queries.
   * @param owner Address of the current owner of a token.
   */
  error ERC721InvalidOwner(address owner);

  /**
   * @dev Indicates a `tokenId` whose `owner` is the zero address.
   * @param tokenId Identifier number of a token.
   */
  error ERC721NonexistentToken(uint256 tokenId);

  /**
   * @dev Indicates an error related to the ownership over a particular token. Used in transfers.
   * @param sender Address whose tokens are being transferred.
   * @param tokenId Identifier number of a token.
   * @param owner Address of the current owner of a token.
   */
  error ERC721IncorrectOwner(address sender, uint256 tokenId, address owner);

  /**
   * @dev Indicates a failure with the token `sender`. Used in transfers.
   * @param sender Address whose tokens are being transferred.
   */
  error ERC721InvalidSender(address sender);

  /**
   * @dev Indicates a failure with the token `receiver`. Used in transfers.
   * @param receiver Address to which tokens are being transferred.
   */
  error ERC721InvalidReceiver(address receiver);

  /**
   * @dev Indicates a failure with the `operator`’s approval. Used in transfers.
   * @param operator Address that may be allowed to operate on tokens without being their owner.
   * @param tokenId Identifier number of a token.
   */
  error ERC721InsufficientApproval(address operator, uint256 tokenId);

  /**
   * @dev Indicates a failure with the `approver` of a token to be approved. Used in approvals.
   * @param approver Address initiating an approval operation.
   */
  error ERC721InvalidApprover(address approver);

  /**
   * @dev Indicates a failure with the `operator` to be approved. Used in approvals.
   * @param operator Address that may be allowed to operate on tokens without being their owner.
   */
  error ERC721InvalidOperator(address operator);
}

/**
 * @dev Standard ERC-1155 Errors
 * Interface of the https://eips.ethereum.org/EIPS/eip-6093[ERC-6093] custom errors for ERC-1155 tokens.
 */
interface IERC1155Errors {
  /**
   * @dev Indicates an error related to the current `balance` of a `sender`. Used in transfers.
   * @param sender Address whose tokens are being transferred.
   * @param balance Current balance for the interacting account.
   * @param needed Minimum amount required to perform a transfer.
   * @param tokenId Identifier number of a token.
   */
  error ERC1155InsufficientBalance(
    address sender,
    uint256 balance,
    uint256 needed,
    uint256 tokenId
  );

  /**
   * @dev Indicates a failure with the token `sender`. Used in transfers.
   * @param sender Address whose tokens are being transferred.
   */
  error ERC1155InvalidSender(address sender);

  /**
   * @dev Indicates a failure with the token `receiver`. Used in transfers.
   * @param receiver Address to which tokens are being transferred.
   */
  error ERC1155InvalidReceiver(address receiver);

  /**
   * @dev Indicates a failure with the `operator`’s approval. Used in transfers.
   * @param operator Address that may be allowed to operate on tokens without being their owner.
   * @param owner Address of the current owner of a token.
   */
  error ERC1155MissingApprovalForAll(address operator, address owner);

  /**
   * @dev Indicates a failure with the `approver` of a token to be approved. Used in approvals.
   * @param approver Address initiating an approval operation.
   */
  error ERC1155InvalidApprover(address approver);

  /**
   * @dev Indicates a failure with the `operator` to be approved. Used in approvals.
   * @param operator Address that may be allowed to operate on tokens without being their owner.
   */
  error ERC1155InvalidOperator(address operator);

  /**
   * @dev Indicates an array length mismatch between ids and values in a safeBatchTransferFrom operation.
   * Used in batch transfers.
   * @param idsLength Length of the array of token identifiers
   * @param valuesLength Length of the array of token amounts
   */
  error ERC1155InvalidArrayLength(uint256 idsLength, uint256 valuesLength);
}

// src/dependencies/openzeppelin/AuthorityUtils.sol

// OpenZeppelin Contracts (last updated v5.3.0) (access/manager/AuthorityUtils.sol)

library AuthorityUtils {
  /**
   * @dev Since `AccessManager` implements an extended IAuthority interface, invoking `canCall` with backwards compatibility
   * for the preexisting `IAuthority` interface requires special care to avoid reverting on insufficient return data.
   * This helper function takes care of invoking `canCall` in a backwards compatible way without reverting.
   */
  function canCallWithDelay(
    address authority,
    address caller,
    address target,
    bytes4 selector
  ) internal view returns (bool immediate, uint32 delay) {
    bytes memory data = abi.encodeCall(IAuthority.canCall, (caller, target, selector));

    assembly ('memory-safe') {
      mstore(0x00, 0x00)
      mstore(0x20, 0x00)

      if staticcall(gas(), authority, add(data, 0x20), mload(data), 0x00, 0x40) {
        immediate := mload(0x00)
        delay := mload(0x20)

        // If delay does not fit in a uint32, return 0 (no delay)
        // equivalent to: if gt(delay, 0xFFFFFFFF) { delay := 0 }
        delay := mul(delay, iszero(shr(32, delay)))
      }
    }
  }
}

// src/dependencies/openzeppelin-upgradeable/ContextUpgradeable.sol

// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract ContextUpgradeable is Initializable {
    function __Context_init() internal onlyInitializing {
    }

    function __Context_init_unchained() internal onlyInitializing {
    }
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

// src/hub/interfaces/IAssetInterestRateStrategy.sol

/// @title IAssetInterestRateStrategy
/// @author Aave Labs
/// @notice Interface of the optimal-usage-based asset interest rate strategy.
interface IAssetInterestRateStrategy is IBasicInterestRateStrategy {
  /// @notice Holds the interest rate data for a given asset.
  /// @dev optimalUsageRatio The optimal usage ratio, in BPS. Maximum and minimum values are defined by `MAX_OPTIMAL_RATIO` and `MIN_OPTIMAL_RATIO`.
  /// @dev baseDrawnRate The base drawn rate, in BPS.
  /// @dev rateGrowthBeforeOptimal The rate growth before the optimal usage ratio, in BPS.
  /// @dev rateGrowthAfterOptimal The rate growth after the optimal usage ratio, in BPS.
  struct InterestRateData {
    uint16 optimalUsageRatio;
    uint32 baseDrawnRate;
    uint32 rateGrowthBeforeOptimal;
    uint32 rateGrowthAfterOptimal;
  }

  /// @notice Emitted when interest rate data is updated for an asset.
  /// @param hub The address of the associated Hub.
  /// @param assetId The identifier of the asset whose interest rate data is updated.
  /// @param optimalUsageRatio The optimal usage ratio, in BPS.
  /// @param baseDrawnRate The base drawn rate, in BPS.
  /// @param rateGrowthBeforeOptimal The rate growth before the optimal usage ratio, in BPS.
  /// @param rateGrowthAfterOptimal The rate growth after the optimal usage ratio, in BPS.
  event UpdateInterestRateData(
    address indexed hub,
    uint256 indexed assetId,
    uint256 optimalUsageRatio,
    uint256 baseDrawnRate,
    uint256 rateGrowthBeforeOptimal,
    uint256 rateGrowthAfterOptimal
  );

  /// @notice Thrown when the given address is invalid.
  error InvalidAddress();

  /// @notice Thrown when the caller is not the Hub.
  error OnlyHub();

  /// @notice Thrown when the max possible rate is greater than `MAX_ALLOWED_DRAWN_RATE`.
  error InvalidMaxDrawnRate();

  /// @notice Thrown when the optimal usage ratio is less than `MIN_OPTIMAL_RATIO` or greater than `MAX_OPTIMAL_RATIO`.
  error InvalidOptimalUsageRatio();

  /// @notice Returns the full InterestRateData struct for the given asset.
  /// @param assetId The identifier of the asset for which to get the data.
  /// @return The InterestRateData struct for the given asset, all in BPS.
  function getInterestRateData(uint256 assetId) external view returns (InterestRateData memory);

  /// @notice Returns the optimal usage rate for the given asset.
  /// @param assetId The identifier of the asset for which to get the optimal usage ratio.
  /// @return The optimal usage ratio, in BPS.
  function getOptimalUsageRatio(uint256 assetId) external view returns (uint256);

  /// @notice Returns the base drawn rate.
  /// @param assetId The identifier of the asset for which to get the base drawn rate.
  /// @return The base drawn rate, in BPS.
  function getBaseDrawnRate(uint256 assetId) external view returns (uint256);

  /// @notice Returns the rate growth before the optimal usage ratio.
  /// @dev Applicable when usage ratio > 0 and <= OPTIMAL_USAGE_RATIO.
  /// @param assetId The identifier of the asset for which to get the rate growth before the optimal usage ratio.
  /// @return The rate growth, in BPS.
  function getRateGrowthBeforeOptimal(uint256 assetId) external view returns (uint256);

  /// @notice Returns the rate growth after the optimal usage ratio.
  /// @dev Applicable when usage ratio > OPTIMAL_USAGE_RATIO.
  /// @param assetId The identifier of the asset for which to get the rate growth after the optimal usage ratio.
  /// @return The rate growth, in BPS.
  function getRateGrowthAfterOptimal(uint256 assetId) external view returns (uint256);

  /// @notice Returns the maximum drawn rate.
  /// @param assetId The identifier of the asset for which to get the maximum drawn rate.
  /// @return The maximum drawn rate, in BPS.
  function getMaxDrawnRate(uint256 assetId) external view returns (uint256);

  /// @notice Returns the maximum allowed value for a drawn rate.
  /// @return The maximum drawn rate, in BPS.
  function MAX_ALLOWED_DRAWN_RATE() external view returns (uint256);

  /// @notice Returns the minimum optimal usage ratio.
  /// @return The minimum optimal usage ratio, expressed in BPS.
  function MIN_OPTIMAL_RATIO() external view returns (uint256);

  /// @notice Returns the maximum optimal usage ratio.
  /// @return The maximum optimal usage ratio, expressed in BPS.
  function MAX_OPTIMAL_RATIO() external view returns (uint256);

  /// @notice Returns the address of the Hub.
  function HUB() external view returns (address);
}

// src/dependencies/openzeppelin/IERC20Metadata.sol

// OpenZeppelin Contracts (last updated v5.4.0) (token/ERC20/extensions/IERC20Metadata.sol)

/**
 * @dev Interface for the optional metadata functions from the ERC-20 standard.
 */
interface IERC20Metadata is IERC20 {
  /**
   * @dev Returns the name of the token.
   */
  function name() external view returns (string memory);

  /**
   * @dev Returns the symbol of the token.
   */
  function symbol() external view returns (string memory);

  /**
   * @dev Returns the decimals places of the token.
   */
  function decimals() external view returns (uint8);
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

// src/hub/interfaces/IHub.sol

/// @title IHub
/// @author Aave Labs
/// @notice Full interface for the Hub.
interface IHub is IHubBase, IAccessManaged {
  /// @notice Asset position and configuration data.
  /// @dev liquidity The liquidity available to be accessed, expressed in asset units.
  /// @dev realizedFees The amount of fees realized but not yet minted, expressed in asset units.
  /// @dev decimals The number of decimals of the underlying asset.
  /// @dev addedShares The total shares added across all spokes.
  /// @dev swept The outstanding liquidity which has been invested by the reinvestment controller, expressed in asset units.
  /// @dev premiumOffsetRay The total premium offset across all spokes, used to calculate the premium, expressed in asset units and scaled by RAY.
  /// @dev drawnShares The total drawn shares across all spokes.
  /// @dev premiumShares The total premium shares across all spokes.
  /// @dev liquidityFee The protocol fee charged on drawn and premium liquidity growth, expressed in BPS.
  /// @dev drawnIndex The drawn index which monotonically increases according to the drawn rate, expressed in RAY.
  /// @dev drawnRate The rate at which drawn assets grow, expressed in RAY.
  /// @dev lastUpdateTimestamp The timestamp of the last accrual.
  /// @dev underlying The address of the underlying asset.
  /// @dev irStrategy The address of the interest rate strategy.
  /// @dev reinvestmentController The address of the reinvestment controller.
  /// @dev feeReceiver The address of the fee receiver spoke.
  /// @dev deficitRay The amount of outstanding bad debt across all spokes, expressed in asset units and scaled by RAY.
  struct Asset {
    uint120 liquidity;
    uint120 realizedFees;
    uint8 decimals;
    //
    uint120 addedShares;
    uint120 swept;
    //
    int200 premiumOffsetRay;
    //
    uint120 drawnShares;
    uint120 premiumShares;
    uint16 liquidityFee;
    //
    uint120 drawnIndex;
    uint96 drawnRate;
    uint40 lastUpdateTimestamp;
    //
    address underlying;
    //
    address irStrategy;
    //
    address reinvestmentController;
    //
    address feeReceiver;
    //
    uint200 deficitRay;
  }

  /// @notice Asset configuration. Subset of the `Asset` struct.
  struct AssetConfig {
    address feeReceiver;
    uint16 liquidityFee;
    address irStrategy;
    address reinvestmentController;
  }

  /// @notice Spoke position and configuration data.
  /// @dev drawnShares The drawn shares of a spoke for a given asset.
  /// @dev premiumShares The premium shares of a spoke for a given asset.
  /// @dev premiumOffsetRay The premium offset of a spoke for a given asset, used to calculate the premium, expressed in asset units and scaled by RAY.
  /// @dev addedShares The added shares of a spoke for a given asset.
  /// @dev addCap The maximum amount that can be added by a spoke, expressed in whole assets (not scaled by decimals). A value of `MAX_ALLOWED_SPOKE_CAP` indicates no cap.
  /// @dev drawCap The maximum amount that can be drawn by a spoke, expressed in whole assets (not scaled by decimals). A value of `MAX_ALLOWED_SPOKE_CAP` indicates no cap.
  /// @dev riskPremiumThreshold The maximum ratio of premium to drawn shares a spoke can have, expressed in BPS. A value of `MAX_RISK_PREMIUM_THRESHOLD` indicates no threshold.
  /// @dev active True if the Spoke is allowed to perform any action.
  /// @dev halted True if the Spoke is prevented from performing actions that instantly update liquidity.
  /// @dev deficitRay The deficit reported by a spoke for a given asset, expressed in asset units and scaled by RAY.
  struct SpokeData {
    uint120 drawnShares;
    uint120 premiumShares;
    //
    int200 premiumOffsetRay;
    //
    uint120 addedShares;
    uint40 addCap;
    uint40 drawCap;
    uint24 riskPremiumThreshold;
    bool active;
    bool halted;
    //
    uint200 deficitRay;
  }

  /// @notice Spoke configuration data. Subset of the `SpokeData` struct.
  struct SpokeConfig {
    uint40 addCap;
    uint40 drawCap;
    uint24 riskPremiumThreshold;
    bool active;
    bool halted;
  }

  /// @notice Emitted when an asset is added.
  /// @param assetId The identifier of the asset.
  /// @param underlying The address of the underlying asset.
  /// @param decimals The number of decimals of the asset.
  event AddAsset(uint256 indexed assetId, address indexed underlying, uint8 decimals);

  /// @notice Emitted when an asset is updated.
  /// @param assetId The identifier of the asset.
  /// @param drawnIndex The new drawn index of the asset.
  /// @param drawnRate The new drawn rate of the asset.
  /// @param accruedFees The accrued fees of the asset since the last mint.
  event UpdateAsset(
    uint256 indexed assetId,
    uint256 drawnIndex,
    uint256 drawnRate,
    uint256 accruedFees
  );

  /// @notice Emitted when an asset configuration is updated.
  /// @param assetId The identifier of the asset.
  /// @param config The new asset configuration struct.
  event UpdateAssetConfig(uint256 indexed assetId, AssetConfig config);

  /// @notice Emitted when a spoke is added.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  event AddSpoke(uint256 indexed assetId, address indexed spoke);

  /// @notice Emitted when a spoke configuration is updated.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @param config The new spoke configuration struct.
  event UpdateSpokeConfig(uint256 indexed assetId, address indexed spoke, SpokeConfig config);

  /// @notice Emitted when fees are minted to the fee receiver spoke.
  /// @param assetId The identifier of the asset.
  /// @param feeReceiver The address of the current fee receiver spoke.
  /// @param shares The amount of shares minted.
  /// @param assets The amount of assets used to mint the shares.
  event MintFeeShares(
    uint256 indexed assetId,
    address indexed feeReceiver,
    uint256 shares,
    uint256 assets
  );

  /// @notice Emitted when liquidity is invested by the reinvestment controller.
  /// @param assetId The identifier of the asset.
  /// @param reinvestmentController The active asset controller.
  /// @param amount The amount invested.
  event Sweep(uint256 indexed assetId, address indexed reinvestmentController, uint256 amount);

  /// @notice Emitted when liquidity is reclaimed (from swept liquidity) by the reinvestment controller.
  /// @param assetId The identifier of the asset.
  /// @param reinvestmentController The active asset controller.
  /// @param amount The amount reclaimed.
  event Reclaim(uint256 indexed assetId, address indexed reinvestmentController, uint256 amount);

  /// @notice Emitted when a deficit is eliminated.
  /// @param assetId The identifier of the asset.
  /// @param callerSpoke The spoke that eliminated the deficit using its added shares.
  /// @param coveredSpoke The spoke for which the deficit was eliminated.
  /// @param shares The amount of shares removed.
  /// @param deficitAmountRay The amount of deficit eliminated, expressed in asset units and scaled by RAY.
  event EliminateDeficit(
    uint256 indexed assetId,
    address indexed callerSpoke,
    address indexed coveredSpoke,
    uint256 shares,
    uint256 deficitAmountRay
  );

  /// @notice Thrown when an underlying asset is already listed.
  error UnderlyingAlreadyListed();

  /// @notice Thrown when an asset is not listed.
  error AssetNotListed();

  /// @notice Thrown when the add cap is exceeded.
  /// @param addCap The current `addCap` of the asset, expressed in whole assets (not scaled by decimals).
  error AddCapExceeded(uint256 addCap);

  /// @notice Thrown when the available liquidity is insufficient.
  /// @param liquidity The current available liquidity.
  error InsufficientLiquidity(uint256 liquidity);

  /// @notice Thrown when the transferred liquidity is insufficient.
  /// @param liquidityNeeded The amount of additional liquidity needed.
  error InsufficientTransferred(uint256 liquidityNeeded);

  /// @notice Thrown when the draw cap is exceeded.
  /// @param drawCap The current `drawCap` of the asset, expressed in whole assets (not scaled by decimals).
  error DrawCapExceeded(uint256 drawCap);

  /// @notice Thrown when a surplus amount of drawn is restored.
  /// @param maxAllowedRestore The maximum allowed drawn amount to restore.
  error SurplusDrawnRestored(uint256 maxAllowedRestore);

  /// @notice Thrown when a surplus amount of premium is restored.
  /// @param maxAllowedRestoreRay The maximum allowed premium amount to restore, expressed in asset units and scaled by RAY.
  error SurplusPremiumRayRestored(uint256 maxAllowedRestoreRay);

  /// @notice Thrown when the premium change is invalid.
  error InvalidPremiumChange();

  /// @notice Thrown when a surplus amount of drawn is reported as deficit.
  /// @param maxAllowedDeficit The maximum allowed drawn to report as deficit.
  error SurplusDrawnDeficitReported(uint256 maxAllowedDeficit);

  /// @notice Thrown when a surplus amount of premium is reported as deficit.
  /// @param maxAllowedDeficitRay The maximum allowed premium to report as deficit, expressed in asset units and scaled by RAY.
  error SurplusPremiumRayDeficitReported(uint256 maxAllowedDeficitRay);

  /// @notice Thrown when a spoke is not active.
  error SpokeNotActive();

  /// @notice Thrown when a spoke is halted.
  error SpokeHalted();

  /// @notice Thrown when a new reinvestment controller is the zero address and the asset has existing swept liquidity.
  error InvalidReinvestmentController();

  /// @notice Thrown when an invalid reinvestment controller attempts to perform a `sweep` action.
  error OnlyReinvestmentController();

  /// @notice Thrown when a spoke being added is already listed.
  error SpokeAlreadyListed();

  /// @notice Thrown when a spoke being updated is not listed.
  error SpokeNotListed();

  /// @notice Thrown when the amount is invalid.
  error InvalidAmount();

  /// @notice Thrown when the shares amount is invalid.
  error InvalidShares();

  /// @notice Thrown when an input address is invalid.
  error InvalidAddress();

  /// @notice Thrown if the liquidity fee is invalid when updating an asset configuration.
  error InvalidLiquidityFee();

  /// @notice Thrown when the asset decimals exceed the maximum allowed decimals.
  error InvalidAssetDecimals();

  /// @notice Thrown if the interest rate strategy or data are invalid when updating an asset configuration.
  /// @dev The `irData` must be empty if the interest rate strategy is not updated.
  error InvalidInterestRateStrategy();

  /// @notice Adds a new asset to the Hub.
  /// @dev The same underlying asset address cannot be added as an asset multiple times.
  /// @dev The fee receiver is added as a new spoke with maximum add cap and zero draw cap.
  /// @param underlying The address of the underlying asset.
  /// @param decimals The number of decimals of `underlying`.
  /// @param feeReceiver The address of the fee receiver spoke.
  /// @param irStrategy The address of the interest rate strategy contract.
  /// @param irData The interest rate data to apply to the given asset encoded in bytes.
  /// @return The unique identifier of the added asset.
  function addAsset(
    address underlying,
    uint8 decimals,
    address feeReceiver,
    address irStrategy,
    bytes calldata irData
  ) external returns (uint256);

  /// @notice Updates the configuration of an asset.
  /// @dev If the fee receiver is updated, adds it as a new spoke with maximum add cap and zero draw cap, and sets old fee receiver caps to zero.
  /// @dev If the fee receiver is updated, accrued fees are minted as shares before the update if their value exceeds one share.
  /// @dev If the interest rate strategy is updated, it is configured with `irData`. Otherwise, `irData` must be empty.
  /// @param assetId The identifier of the asset.
  /// @param config The new configuration for the asset.
  /// @param irData The interest rate data to apply to the given asset, encoded in bytes.
  function updateAssetConfig(
    uint256 assetId,
    AssetConfig calldata config,
    bytes calldata irData
  ) external;

  /// @notice Registers a new spoke for a specific asset in the Hub.
  /// @dev Reverts with `SpokeAlreadyListed` if spoke is already listed.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke to add.
  /// @param params The configuration parameters for the Spoke.
  function addSpoke(uint256 assetId, address spoke, SpokeConfig calldata params) external;

  /// @notice Updates the configuration of a spoke for a specific asset.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke to update.
  /// @param config The new configuration for the Spoke.
  function updateSpokeConfig(uint256 assetId, address spoke, SpokeConfig calldata config) external;

  /// @notice Updates the interest rate strategy for a specified asset.
  /// @param assetId The identifier of the asset.
  /// @param irData The interest rate data to apply to the given asset, encoded in bytes.
  function setInterestRateData(uint256 assetId, bytes calldata irData) external;

  /// @notice Mints shares to the fee receiver from accrued fees.
  /// @dev No op when fees are worth less than one share.
  /// @param assetId The identifier of the asset.
  /// @return The amount of shares minted.
  function mintFeeShares(uint256 assetId) external returns (uint256);

  /// @notice Eliminates deficit by removing added shares of caller spoke.
  /// @dev Only callable by active and authorized spokes.
  /// @param assetId The identifier of the asset.
  /// @param amount The amount of deficit to eliminate.
  /// @param spoke The spoke for which the deficit is eliminated.
  /// @return The amount of added shares removed.
  /// @return The amount of deficit eliminated, expressed in asset units.
  function eliminateDeficit(
    uint256 assetId,
    uint256 amount,
    address spoke
  ) external returns (uint256, uint256);

  /// @notice Allows a spoke to transfer its added shares of an asset to another spoke.
  /// @dev Only callable by spokes.
  /// @param assetId The identifier of the asset.
  /// @param shares The amount of shares to move.
  /// @param toSpoke The address of the recipient spoke.
  function transferShares(uint256 assetId, uint256 shares, address toSpoke) external;

  /// @notice Sweeps an amount of liquidity of the corresponding asset and sends it to the configured reinvestment controller.
  /// @dev The controller handles the actual reinvestment of funds, redistribution of interest, and investment caps.
  /// @param assetId The identifier of the asset.
  /// @param amount The amount to sweep.
  function sweep(uint256 assetId, uint256 amount) external;

  /// @notice Reclaims an amount of liquidity of the corresponding asset from the configured reinvestment controller.
  /// @dev The controller can only reclaim up to swept amount. All accrued interest is distributed offchain.
  /// @dev Underlying assets must be transferred to the Hub before invocation.
  /// @dev Extra untracked underlying liquidity in the Hub can be skimmed into the Hub's liquidity accounting through this action.
  /// @param assetId The identifier of the asset.
  /// @param amount The amount to reclaim.
  function reclaim(uint256 assetId, uint256 amount) external;

  /// @notice Returns whether the underlying is listed as an asset.
  /// @param underlying The address of the underlying asset.
  /// @return True if the underlying asset is listed.
  function isUnderlyingListed(address underlying) external view returns (bool);

  /// @notice Returns the number of listed assets.
  function getAssetCount() external view returns (uint256);

  /// @notice Returns information regarding the specified asset.
  /// @dev `drawnIndex`, `drawnRate` and `lastUpdateTimestamp` can be outdated due to passage of time.
  /// @param assetId The identifier of the asset.
  /// @return The asset struct.
  function getAsset(uint256 assetId) external view returns (Asset memory);

  /// @notice Returns the asset configuration for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The asset configuration struct.
  function getAssetConfig(uint256 assetId) external view returns (AssetConfig memory);

  /// @notice Returns the accrued fees for the asset, expressed in asset units.
  /// @dev Accrued fees are excluded from total added assets.
  /// @param assetId The identifier of the asset.
  /// @return The amount of accrued fees.
  function getAssetAccruedFees(uint256 assetId) external view returns (uint256);

  /// @notice Returns the amount of liquidity swept by the reinvestment controller for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The amount of liquidity swept.
  function getAssetSwept(uint256 assetId) external view returns (uint256);

  /// @notice Calculates the current drawn rate for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @return The current drawn rate of the asset.
  function getAssetDrawnRate(uint256 assetId) external view returns (uint256);

  /// @notice Returns the number of spokes listed for the specified asset.
  /// @param assetId The identifier of the asset.
  function getSpokeCount(uint256 assetId) external view returns (uint256);

  /// @notice Returns whether the Spoke is listed for the specified asset.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return True if the Spoke is listed.
  function isSpokeListed(uint256 assetId, address spoke) external view returns (bool);

  /// @notice Returns the address of the Spoke for an asset at the given index.
  /// @param assetId The identifier of the asset.
  /// @param index The index of the Spoke.
  /// @return The address of the Spoke.
  function getSpokeAddress(uint256 assetId, uint256 index) external view returns (address);

  /// @notice Returns the Spoke data struct.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The spoke data struct.
  function getSpoke(uint256 assetId, address spoke) external view returns (SpokeData memory);

  /// @notice Returns the Spoke configuration struct.
  /// @param assetId The identifier of the asset.
  /// @param spoke The address of the Spoke.
  /// @return The spoke configuration struct.
  function getSpokeConfig(
    uint256 assetId,
    address spoke
  ) external view returns (SpokeConfig memory);

  /// @notice Returns the maximum allowed number of decimals for the underlying asset.
  /// @return The maximum number of decimals (inclusive).
  function MAX_ALLOWED_UNDERLYING_DECIMALS() external view returns (uint8);

  /// @notice Returns the minimum allowed number of decimals for the underlying asset.
  /// @return The minimum number of decimals (inclusive).
  function MIN_ALLOWED_UNDERLYING_DECIMALS() external view returns (uint8);

  /// @notice Returns the maximum value for any spoke cap (add or draw).
  /// @dev The value is not inclusive; using the maximum value indicates no cap.
  /// @return The maximum cap value, expressed in asset units.
  function MAX_ALLOWED_SPOKE_CAP() external view returns (uint40);

  /// @notice Returns the maximum value for any spoke risk premium threshold.
  /// @dev The value is not inclusive; using the maximum value indicates no threshold.
  /// @return The maximum risk premium threshold, expressed in BPS.
  function MAX_RISK_PREMIUM_THRESHOLD() external view returns (uint24);
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

// src/hub/AssetInterestRateStrategy.sol

/// @title AssetInterestRateStrategy
/// @author Aave Labs
/// @notice Manages the optimal-usage-based interest rate strategy for an asset.
/// @dev Strategies are Hub-specific, due to the usage of asset identifier as index of the `_interestRateData` mapping.
contract AssetInterestRateStrategy is IAssetInterestRateStrategy {
  using WadRayMath for *;

  /// @inheritdoc IAssetInterestRateStrategy
  uint256 public constant MAX_ALLOWED_DRAWN_RATE = 1000_00;

  /// @inheritdoc IAssetInterestRateStrategy
  uint256 public constant MIN_OPTIMAL_RATIO = 1_00;

  /// @inheritdoc IAssetInterestRateStrategy
  uint256 public constant MAX_OPTIMAL_RATIO = 99_00;

  /// @inheritdoc IAssetInterestRateStrategy
  address public immutable HUB;

  /// @dev Map of asset identifiers to their interest rate data.
  mapping(uint256 assetId => InterestRateData) internal _interestRateData;

  /// @dev Constructor.
  /// @param hub_ The address of the associated Hub.
  constructor(address hub_) {
    require(hub_ != address(0), InvalidAddress());
    HUB = hub_;
  }

  /// @notice Sets the interest rate parameters for a specified asset.
  /// @param assetId The identifier of the asset.
  /// @param data The encoded parameters containing BPS data used to configure the interest rate of the asset.
  function setInterestRateData(uint256 assetId, bytes calldata data) external {
    require(HUB == msg.sender, OnlyHub());
    InterestRateData memory rateData = abi.decode(data, (InterestRateData));
    require(
      MIN_OPTIMAL_RATIO <= rateData.optimalUsageRatio &&
        rateData.optimalUsageRatio <= MAX_OPTIMAL_RATIO,
      InvalidOptimalUsageRatio()
    );
    require(
      rateData.baseDrawnRate + rateData.rateGrowthBeforeOptimal + rateData.rateGrowthAfterOptimal <=
        MAX_ALLOWED_DRAWN_RATE,
      InvalidMaxDrawnRate()
    );

    _interestRateData[assetId] = rateData;

    emit UpdateInterestRateData(
      HUB,
      assetId,
      rateData.optimalUsageRatio,
      rateData.baseDrawnRate,
      rateData.rateGrowthBeforeOptimal,
      rateData.rateGrowthAfterOptimal
    );
  }

  /// @inheritdoc IAssetInterestRateStrategy
  function getInterestRateData(uint256 assetId) external view returns (InterestRateData memory) {
    return _interestRateData[assetId];
  }

  /// @inheritdoc IAssetInterestRateStrategy
  function getOptimalUsageRatio(uint256 assetId) external view returns (uint256) {
    return _interestRateData[assetId].optimalUsageRatio;
  }

  /// @inheritdoc IAssetInterestRateStrategy
  function getBaseDrawnRate(uint256 assetId) external view returns (uint256) {
    return _interestRateData[assetId].baseDrawnRate;
  }

  /// @inheritdoc IAssetInterestRateStrategy
  function getRateGrowthBeforeOptimal(uint256 assetId) external view returns (uint256) {
    return _interestRateData[assetId].rateGrowthBeforeOptimal;
  }

  /// @inheritdoc IAssetInterestRateStrategy
  function getRateGrowthAfterOptimal(uint256 assetId) external view returns (uint256) {
    return _interestRateData[assetId].rateGrowthAfterOptimal;
  }

  /// @inheritdoc IAssetInterestRateStrategy
  function getMaxDrawnRate(uint256 assetId) external view returns (uint256) {
    return
      _interestRateData[assetId].baseDrawnRate +
      _interestRateData[assetId].rateGrowthBeforeOptimal +
      _interestRateData[assetId].rateGrowthAfterOptimal;
  }

  /// @inheritdoc IBasicInterestRateStrategy
  function calculateInterestRate(
    uint256 assetId,
    uint256 liquidity,
    uint256 drawn,
    uint256 /* deficit */,
    uint256 swept
  ) external view returns (uint256) {
    InterestRateData memory rateData = _interestRateData[assetId];
    require(rateData.optimalUsageRatio > 0, InterestRateDataNotSet(assetId));

    uint256 currentDrawnRateRay = rateData.baseDrawnRate.bpsToRay();
    if (drawn == 0) {
      return currentDrawnRateRay;
    }

    uint256 usageRatioRay = drawn.rayDivUp(liquidity + drawn + swept);
    uint256 optimalUsageRatioRay = rateData.optimalUsageRatio.bpsToRay();

    if (usageRatioRay <= optimalUsageRatioRay) {
      currentDrawnRateRay += rateData
        .rateGrowthBeforeOptimal
        .bpsToRay()
        .rayMulUp(usageRatioRay)
        .rayDivUp(optimalUsageRatioRay);
    } else {
      currentDrawnRateRay +=
        rateData.rateGrowthBeforeOptimal.bpsToRay() +
        rateData
          .rateGrowthAfterOptimal
          .bpsToRay()
          .rayMulUp(usageRatioRay - optimalUsageRatioRay)
          .rayDivUp(WadRayMath.RAY - optimalUsageRatioRay);
    }

    return currentDrawnRateRay;
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

// src/hub/libraries/SharesMath.sol

/// @title SharesMath library
/// @author Aave Labs
/// @notice Implements the logic to convert between assets and shares.
/// @dev Utilizes virtual assets and shares to mitigate share manipulation attacks.
library SharesMath {
  using Math for uint256;

  uint256 internal constant VIRTUAL_ASSETS = 1e6;
  uint256 internal constant VIRTUAL_SHARES = 1e6;

  /// @notice Converts an amount of assets to the equivalent amount of shares, rounding down.
  function toSharesDown(
    uint256 assets,
    uint256 totalAssets,
    uint256 totalShares
  ) internal pure returns (uint256) {
    return
      assets.mulDiv(
        totalShares + VIRTUAL_SHARES,
        totalAssets + VIRTUAL_ASSETS,
        Math.Rounding.Floor
      );
  }

  /// @notice Converts an amount of shares to the equivalent amount of assets, rounding down.
  function toAssetsDown(
    uint256 shares,
    uint256 totalAssets,
    uint256 totalShares
  ) internal pure returns (uint256) {
    return
      shares.mulDiv(
        totalAssets + VIRTUAL_ASSETS,
        totalShares + VIRTUAL_SHARES,
        Math.Rounding.Floor
      );
  }

  /// @notice Converts an amount of assets to the equivalent amount of shares, rounding up.
  function toSharesUp(
    uint256 assets,
    uint256 totalAssets,
    uint256 totalShares
  ) internal pure returns (uint256) {
    return
      assets.mulDiv(totalShares + VIRTUAL_SHARES, totalAssets + VIRTUAL_ASSETS, Math.Rounding.Ceil);
  }

  /// @notice Converts an amount of shares to the equivalent amount of assets, rounding up.
  function toAssetsUp(
    uint256 shares,
    uint256 totalAssets,
    uint256 totalShares
  ) internal pure returns (uint256) {
    return
      shares.mulDiv(totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES, Math.Rounding.Ceil);
  }
}

// src/dependencies/openzeppelin/ERC20.sol

// OpenZeppelin Contracts (last updated v5.5.0) (token/ERC20/ERC20.sol)

/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.openzeppelin.com/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * The default value of {decimals} is 18. To change this, you should override
 * this function so it returns a different value.
 *
 * We have followed general OpenZeppelin Contracts guidelines: functions revert
 * instead returning `false` on failure. This behavior is nonetheless
 * conventional and does not conflict with the expectations of ERC-20
 * applications.
 */
abstract contract ERC20 is Context, IERC20, IERC20Metadata, IERC20Errors {
  mapping(address account => uint256) private _balances;

  mapping(address account => mapping(address spender => uint256)) private _allowances;

  uint256 private _totalSupply;

  string private _name;
  string private _symbol;

  /**
   * @dev Sets the values for {name} and {symbol}.
   *
   * Both values are immutable: they can only be set once during construction.
   */
  constructor(string memory name_, string memory symbol_) {
    _name = name_;
    _symbol = symbol_;
  }

  /**
   * @dev Returns the name of the token.
   */
  function name() public view virtual returns (string memory) {
    return _name;
  }

  /**
   * @dev Returns the symbol of the token, usually a shorter version of the
   * name.
   */
  function symbol() public view virtual returns (string memory) {
    return _symbol;
  }

  /**
   * @dev Returns the number of decimals used to get its user representation.
   * For example, if `decimals` equals `2`, a balance of `505` tokens should
   * be displayed to a user as `5.05` (`505 / 10 ** 2`).
   *
   * Tokens usually opt for a value of 18, imitating the relationship between
   * Ether and Wei. This is the default value returned by this function, unless
   * it's overridden.
   *
   * NOTE: This information is only used for _display_ purposes: it in
   * no way affects any of the arithmetic of the contract, including
   * {IERC20-balanceOf} and {IERC20-transfer}.
   */
  function decimals() public view virtual returns (uint8) {
    return 18;
  }

  /// @inheritdoc IERC20
  function totalSupply() public view virtual returns (uint256) {
    return _totalSupply;
  }

  /// @inheritdoc IERC20
  function balanceOf(address account) public view virtual returns (uint256) {
    return _balances[account];
  }

  /**
   * @dev See {IERC20-transfer}.
   *
   * Requirements:
   *
   * - `to` cannot be the zero address.
   * - the caller must have a balance of at least `value`.
   */
  function transfer(address to, uint256 value) public virtual returns (bool) {
    address owner = _msgSender();
    _transfer(owner, to, value);
    return true;
  }

  /// @inheritdoc IERC20
  function allowance(address owner, address spender) public view virtual returns (uint256) {
    return _allowances[owner][spender];
  }

  /**
   * @dev See {IERC20-approve}.
   *
   * NOTE: If `value` is the maximum `uint256`, the allowance is not updated on
   * `transferFrom`. This is semantically equivalent to an infinite approval.
   *
   * Requirements:
   *
   * - `spender` cannot be the zero address.
   */
  function approve(address spender, uint256 value) public virtual returns (bool) {
    address owner = _msgSender();
    _approve(owner, spender, value);
    return true;
  }

  /**
   * @dev See {IERC20-transferFrom}.
   *
   * Skips emitting an {Approval} event indicating an allowance update. This is not
   * required by the ERC. See {xref-ERC20-_approve-address-address-uint256-bool-}[_approve].
   *
   * NOTE: Does not update the allowance if the current allowance
   * is the maximum `uint256`.
   *
   * Requirements:
   *
   * - `from` and `to` cannot be the zero address.
   * - `from` must have a balance of at least `value`.
   * - the caller must have allowance for ``from``'s tokens of at least
   * `value`.
   */
  function transferFrom(address from, address to, uint256 value) public virtual returns (bool) {
    address spender = _msgSender();
    _spendAllowance(from, spender, value);
    _transfer(from, to, value);
    return true;
  }

  /**
   * @dev Moves a `value` amount of tokens from `from` to `to`.
   *
   * This internal function is equivalent to {transfer}, and can be used to
   * e.g. implement automatic token fees, slashing mechanisms, etc.
   *
   * Emits a {Transfer} event.
   *
   * NOTE: This function is not virtual, {_update} should be overridden instead.
   */
  function _transfer(address from, address to, uint256 value) internal {
    if (from == address(0)) {
      revert ERC20InvalidSender(address(0));
    }
    if (to == address(0)) {
      revert ERC20InvalidReceiver(address(0));
    }
    _update(from, to, value);
  }

  /**
   * @dev Transfers a `value` amount of tokens from `from` to `to`, or alternatively mints (or burns) if `from`
   * (or `to`) is the zero address. All customizations to transfers, mints, and burns should be done by overriding
   * this function.
   *
   * Emits a {Transfer} event.
   */
  function _update(address from, address to, uint256 value) internal virtual {
    if (from == address(0)) {
      // Overflow check required: The rest of the code assumes that totalSupply never overflows
      _totalSupply += value;
    } else {
      uint256 fromBalance = _balances[from];
      if (fromBalance < value) {
        revert ERC20InsufficientBalance(from, fromBalance, value);
      }
      unchecked {
        // Overflow not possible: value <= fromBalance <= totalSupply.
        _balances[from] = fromBalance - value;
      }
    }

    if (to == address(0)) {
      unchecked {
        // Overflow not possible: value <= totalSupply or value <= fromBalance <= totalSupply.
        _totalSupply -= value;
      }
    } else {
      unchecked {
        // Overflow not possible: balance + value is at most totalSupply, which we know fits into a uint256.
        _balances[to] += value;
      }
    }

    emit Transfer(from, to, value);
  }

  /**
   * @dev Creates a `value` amount of tokens and assigns them to `account`, by transferring it from address(0).
   * Relies on the `_update` mechanism
   *
   * Emits a {Transfer} event with `from` set to the zero address.
   *
   * NOTE: This function is not virtual, {_update} should be overridden instead.
   */
  function _mint(address account, uint256 value) internal {
    if (account == address(0)) {
      revert ERC20InvalidReceiver(address(0));
    }
    _update(address(0), account, value);
  }

  /**
   * @dev Destroys a `value` amount of tokens from `account`, lowering the total supply.
   * Relies on the `_update` mechanism.
   *
   * Emits a {Transfer} event with `to` set to the zero address.
   *
   * NOTE: This function is not virtual, {_update} should be overridden instead
   */
  function _burn(address account, uint256 value) internal {
    if (account == address(0)) {
      revert ERC20InvalidSender(address(0));
    }
    _update(account, address(0), value);
  }

  /**
   * @dev Sets `value` as the allowance of `spender` over the `owner`'s tokens.
   *
   * This internal function is equivalent to `approve`, and can be used to
   * e.g. set automatic allowances for certain subsystems, etc.
   *
   * Emits an {Approval} event.
   *
   * Requirements:
   *
   * - `owner` cannot be the zero address.
   * - `spender` cannot be the zero address.
   *
   * Overrides to this logic should be done to the variant with an additional `bool emitEvent` argument.
   */
  function _approve(address owner, address spender, uint256 value) internal {
    _approve(owner, spender, value, true);
  }

  /**
   * @dev Variant of {_approve} with an optional flag to enable or disable the {Approval} event.
   *
   * By default (when calling {_approve}) the flag is set to true. On the other hand, approval changes made by
   * `_spendAllowance` during the `transferFrom` operation sets the flag to false. This saves gas by not emitting any
   * `Approval` event during `transferFrom` operations.
   *
   * Anyone who wishes to continue emitting `Approval` events on the `transferFrom` operation can force the flag to
   * true using the following override:
   *
   * ```solidity
   * function _approve(address owner, address spender, uint256 value, bool) internal virtual override {
   *     super._approve(owner, spender, value, true);
   * }
   * ```
   *
   * Requirements are the same as {_approve}.
   */
  function _approve(
    address owner,
    address spender,
    uint256 value,
    bool emitEvent
  ) internal virtual {
    if (owner == address(0)) {
      revert ERC20InvalidApprover(address(0));
    }
    if (spender == address(0)) {
      revert ERC20InvalidSpender(address(0));
    }
    _allowances[owner][spender] = value;
    if (emitEvent) {
      emit Approval(owner, spender, value);
    }
  }

  /**
   * @dev Updates `owner`'s allowance for `spender` based on spent `value`.
   *
   * Does not update the allowance value in case of infinite allowance.
   * Revert if not enough allowance is available.
   *
   * Does not emit an {Approval} event.
   */
  function _spendAllowance(address owner, address spender, uint256 value) internal virtual {
    uint256 currentAllowance = allowance(owner, spender);
    if (currentAllowance < type(uint256).max) {
      if (currentAllowance < value) {
        revert ERC20InsufficientAllowance(spender, currentAllowance, value);
      }
      unchecked {
        _approve(owner, spender, currentAllowance - value, false);
      }
    }
  }
}

// src/dependencies/openzeppelin-upgradeable/AccessManagedUpgradeable.sol

// OpenZeppelin Contracts (last updated v5.4.0) (access/manager/AccessManaged.sol)

/**
 * @dev This contract module makes available a {restricted} modifier. Functions decorated with this modifier will be
 * permissioned according to an "authority": a contract like {AccessManager} that follows the {IAuthority} interface,
 * implementing a policy that allows certain callers to access certain functions.
 *
 * IMPORTANT: The `restricted` modifier should never be used on `internal` functions, judiciously used in `public`
 * functions, and ideally only used in `external` functions. See {restricted}.
 */
abstract contract AccessManagedUpgradeable is Initializable, ContextUpgradeable, IAccessManaged {
  /// @custom:storage-location erc7201:openzeppelin.storage.AccessManaged
  struct AccessManagedStorage {
    address _authority;
    bool _consumingSchedule;
  }

  // keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.AccessManaged")) - 1)) & ~bytes32(uint256(0xff))
  bytes32 private constant AccessManagedStorageLocation =
    0xf3177357ab46d8af007ab3fdb9af81da189e1068fefdc0073dca88a2cab40a00;

  function _getAccessManagedStorage() private pure returns (AccessManagedStorage storage $) {
    assembly {
      $.slot := AccessManagedStorageLocation
    }
  }

  /**
   * @dev Initializes the contract connected to an initial authority.
   */
  function __AccessManaged_init(address initialAuthority) internal onlyInitializing {
    __AccessManaged_init_unchained(initialAuthority);
  }

  function __AccessManaged_init_unchained(address initialAuthority) internal onlyInitializing {
    _setAuthority(initialAuthority);
  }

  /**
   * @dev Restricts access to a function as defined by the connected Authority for this contract and the
   * caller and selector of the function that entered the contract.
   *
   * [IMPORTANT]
   * ====
   * In general, this modifier should only be used on `external` functions. It is okay to use it on `public`
   * functions that are used as external entry points and are not called internally. Unless you know what you're
   * doing, it should never be used on `internal` functions. Failure to follow these rules can have critical security
   * implications! This is because the permissions are determined by the function that entered the contract, i.e. the
   * function at the bottom of the call stack, and not the function where the modifier is visible in the source code.
   * ====
   *
   * [WARNING]
   * ====
   * Avoid adding this modifier to the https://docs.soliditylang.org/en/v0.8.20/contracts.html#receive-ether-function[`receive()`]
   * function or the https://docs.soliditylang.org/en/v0.8.20/contracts.html#fallback-function[`fallback()`]. These
   * functions are the only execution paths where a function selector cannot be unambiguously determined from the calldata
   * since the selector defaults to `0x00000000` in the `receive()` function and similarly in the `fallback()` function
   * if no calldata is provided. (See {_checkCanCall}).
   *
   * The `receive()` function will always panic whereas the `fallback()` may panic depending on the calldata length.
   * ====
   */
  modifier restricted() {
    _checkCanCall(_msgSender(), _msgData());
    _;
  }

  /// @inheritdoc IAccessManaged
  function authority() public view virtual returns (address) {
    AccessManagedStorage storage $ = _getAccessManagedStorage();
    return $._authority;
  }

  /// @inheritdoc IAccessManaged
  function setAuthority(address newAuthority) public virtual {
    address caller = _msgSender();
    if (caller != authority()) {
      revert AccessManagedUnauthorized(caller);
    }
    if (newAuthority.code.length == 0) {
      revert AccessManagedInvalidAuthority(newAuthority);
    }
    _setAuthority(newAuthority);
  }

  /// @inheritdoc IAccessManaged
  function isConsumingScheduledOp() public view returns (bytes4) {
    AccessManagedStorage storage $ = _getAccessManagedStorage();
    return $._consumingSchedule ? this.isConsumingScheduledOp.selector : bytes4(0);
  }

  /**
   * @dev Transfers control to a new authority. Internal function with no access restriction. Allows bypassing the
   * permissions set by the current authority.
   */
  function _setAuthority(address newAuthority) internal virtual {
    AccessManagedStorage storage $ = _getAccessManagedStorage();
    $._authority = newAuthority;
    emit AuthorityUpdated(newAuthority);
  }

  /**
   * @dev Reverts if the caller is not allowed to call the function identified by a selector. Panics if the calldata
   * is less than 4 bytes long.
   */
  function _checkCanCall(address caller, bytes calldata data) internal virtual {
    AccessManagedStorage storage $ = _getAccessManagedStorage();
    (bool immediate, uint32 delay) = AuthorityUtils.canCallWithDelay(
      authority(),
      caller,
      address(this),
      bytes4(data[0:4])
    );
    if (!immediate) {
      if (delay > 0) {
        $._consumingSchedule = true;
        IAccessManager(authority()).consumeScheduledOp(caller, data);
        $._consumingSchedule = false;
      } else {
        revert AccessManagedUnauthorized(caller);
      }
    }
  }
}

// src/dependencies/openzeppelin/Arrays.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/Arrays.sol)
// This file was procedurally generated from scripts/generate/templates/Arrays.js.

/**
 * @dev Collection of functions related to array types.
 */
library Arrays {
  using SlotDerivation for bytes32;
  using StorageSlot for bytes32;

  /**
   * @dev Sort an array of uint256 (in memory) following the provided comparator function.
   *
   * This function does the sorting "in place", meaning that it overrides the input. The object is returned for
   * convenience, but that returned value can be discarded safely if the caller has a memory pointer to the array.
   *
   * NOTE: this function's cost is `O(n · log(n))` in average and `O(n²)` in the worst case, with n the length of the
   * array. Using it in view functions that are executed through `eth_call` is safe, but one should be very careful
   * when executing this as part of a transaction. If the array being sorted is too large, the sort operation may
   * consume more gas than is available in a block, leading to potential DoS.
   *
   * IMPORTANT: Consider memory side-effects when using custom comparator functions that access memory in an unsafe way.
   */
  function sort(
    uint256[] memory array,
    function(uint256, uint256) pure returns (bool) comp
  ) internal pure returns (uint256[] memory) {
    _quickSort(_begin(array), _end(array), comp);
    return array;
  }

  /**
   * @dev Variant of {sort} that sorts an array of uint256 in increasing order.
   */
  function sort(uint256[] memory array) internal pure returns (uint256[] memory) {
    sort(array, Comparators.lt);
    return array;
  }

  /**
   * @dev Sort an array of address (in memory) following the provided comparator function.
   *
   * This function does the sorting "in place", meaning that it overrides the input. The object is returned for
   * convenience, but that returned value can be discarded safely if the caller has a memory pointer to the array.
   *
   * NOTE: this function's cost is `O(n · log(n))` in average and `O(n²)` in the worst case, with n the length of the
   * array. Using it in view functions that are executed through `eth_call` is safe, but one should be very careful
   * when executing this as part of a transaction. If the array being sorted is too large, the sort operation may
   * consume more gas than is available in a block, leading to potential DoS.
   *
   * IMPORTANT: Consider memory side-effects when using custom comparator functions that access memory in an unsafe way.
   */
  function sort(
    address[] memory array,
    function(address, address) pure returns (bool) comp
  ) internal pure returns (address[] memory) {
    sort(_castToUint256Array(array), _castToUint256Comp(comp));
    return array;
  }

  /**
   * @dev Variant of {sort} that sorts an array of address in increasing order.
   */
  function sort(address[] memory array) internal pure returns (address[] memory) {
    sort(_castToUint256Array(array), Comparators.lt);
    return array;
  }

  /**
   * @dev Sort an array of bytes32 (in memory) following the provided comparator function.
   *
   * This function does the sorting "in place", meaning that it overrides the input. The object is returned for
   * convenience, but that returned value can be discarded safely if the caller has a memory pointer to the array.
   *
   * NOTE: this function's cost is `O(n · log(n))` in average and `O(n²)` in the worst case, with n the length of the
   * array. Using it in view functions that are executed through `eth_call` is safe, but one should be very careful
   * when executing this as part of a transaction. If the array being sorted is too large, the sort operation may
   * consume more gas than is available in a block, leading to potential DoS.
   *
   * IMPORTANT: Consider memory side-effects when using custom comparator functions that access memory in an unsafe way.
   */
  function sort(
    bytes32[] memory array,
    function(bytes32, bytes32) pure returns (bool) comp
  ) internal pure returns (bytes32[] memory) {
    sort(_castToUint256Array(array), _castToUint256Comp(comp));
    return array;
  }

  /**
   * @dev Variant of {sort} that sorts an array of bytes32 in increasing order.
   */
  function sort(bytes32[] memory array) internal pure returns (bytes32[] memory) {
    sort(_castToUint256Array(array), Comparators.lt);
    return array;
  }

  /**
   * @dev Performs a quick sort of a segment of memory. The segment sorted starts at `begin` (inclusive), and stops
   * at end (exclusive). Sorting follows the `comp` comparator.
   *
   * Invariant: `begin <= end`. This is the case when initially called by {sort} and is preserved in subcalls.
   *
   * IMPORTANT: Memory locations between `begin` and `end` are not validated/zeroed. This function should
   * be used only if the limits are within a memory array.
   */
  function _quickSort(
    uint256 begin,
    uint256 end,
    function(uint256, uint256) pure returns (bool) comp
  ) private pure {
    unchecked {
      if (end - begin < 0x40) return;

      // Use first element as pivot
      uint256 pivot = _mload(begin);
      // Position where the pivot should be at the end of the loop
      uint256 pos = begin;

      for (uint256 it = begin + 0x20; it < end; it += 0x20) {
        if (comp(_mload(it), pivot)) {
          // If the value stored at the iterator's position comes before the pivot, we increment the
          // position of the pivot and move the value there.
          pos += 0x20;
          _swap(pos, it);
        }
      }

      _swap(begin, pos); // Swap pivot into place
      _quickSort(begin, pos, comp); // Sort the left side of the pivot
      _quickSort(pos + 0x20, end, comp); // Sort the right side of the pivot
    }
  }

  /**
   * @dev Pointer to the memory location of the first element of `array`.
   */
  function _begin(uint256[] memory array) private pure returns (uint256 ptr) {
    assembly ('memory-safe') {
      ptr := add(array, 0x20)
    }
  }

  /**
   * @dev Pointer to the memory location of the first memory word (32bytes) after `array`. This is the memory word
   * that comes just after the last element of the array.
   */
  function _end(uint256[] memory array) private pure returns (uint256 ptr) {
    unchecked {
      return _begin(array) + array.length * 0x20;
    }
  }

  /**
   * @dev Load memory word (as a uint256) at location `ptr`.
   */
  function _mload(uint256 ptr) private pure returns (uint256 value) {
    assembly {
      value := mload(ptr)
    }
  }

  /**
   * @dev Swaps the elements memory location `ptr1` and `ptr2`.
   */
  function _swap(uint256 ptr1, uint256 ptr2) private pure {
    assembly {
      let value1 := mload(ptr1)
      let value2 := mload(ptr2)
      mstore(ptr1, value2)
      mstore(ptr2, value1)
    }
  }

  /// @dev Helper: low level cast address memory array to uint256 memory array
  function _castToUint256Array(
    address[] memory input
  ) private pure returns (uint256[] memory output) {
    assembly {
      output := input
    }
  }

  /// @dev Helper: low level cast bytes32 memory array to uint256 memory array
  function _castToUint256Array(
    bytes32[] memory input
  ) private pure returns (uint256[] memory output) {
    assembly {
      output := input
    }
  }

  /// @dev Helper: low level cast address comp function to uint256 comp function
  function _castToUint256Comp(
    function(address, address) pure returns (bool) input
  ) private pure returns (function(uint256, uint256) pure returns (bool) output) {
    assembly {
      output := input
    }
  }

  /// @dev Helper: low level cast bytes32 comp function to uint256 comp function
  function _castToUint256Comp(
    function(bytes32, bytes32) pure returns (bool) input
  ) private pure returns (function(uint256, uint256) pure returns (bool) output) {
    assembly {
      output := input
    }
  }

  /**
   * @dev Searches a sorted `array` and returns the first index that contains
   * a value greater or equal to `element`. If no such index exists (i.e. all
   * values in the array are strictly less than `element`), the array length is
   * returned. Time complexity O(log n).
   *
   * NOTE: The `array` is expected to be sorted in ascending order, and to
   * contain no repeated elements.
   *
   * IMPORTANT: Deprecated. This implementation behaves as {lowerBound} but lacks
   * support for repeated elements in the array. The {lowerBound} function should
   * be used instead.
   */
  function findUpperBound(
    uint256[] storage array,
    uint256 element
  ) internal view returns (uint256) {
    uint256 low = 0;
    uint256 high = array.length;

    if (high == 0) {
      return 0;
    }

    while (low < high) {
      uint256 mid = Math.average(low, high);

      // Note that mid will always be strictly less than high (i.e. it will be a valid array index)
      // because Math.average rounds towards zero (it does integer division with truncation).
      if (unsafeAccess(array, mid).value > element) {
        high = mid;
      } else {
        low = mid + 1;
      }
    }

    // At this point `low` is the exclusive upper bound. We will return the inclusive upper bound.
    if (low > 0 && unsafeAccess(array, low - 1).value == element) {
      return low - 1;
    } else {
      return low;
    }
  }

  /**
   * @dev Searches an `array` sorted in ascending order and returns the first
   * index that contains a value greater or equal than `element`. If no such index
   * exists (i.e. all values in the array are strictly less than `element`), the array
   * length is returned. Time complexity O(log n).
   *
   * See C++'s https://en.cppreference.com/w/cpp/algorithm/lower_bound[lower_bound].
   */
  function lowerBound(uint256[] storage array, uint256 element) internal view returns (uint256) {
    uint256 low = 0;
    uint256 high = array.length;

    if (high == 0) {
      return 0;
    }

    while (low < high) {
      uint256 mid = Math.average(low, high);

      // Note that mid will always be strictly less than high (i.e. it will be a valid array index)
      // because Math.average rounds towards zero (it does integer division with truncation).
      if (unsafeAccess(array, mid).value < element) {
        // this cannot overflow because mid < high
        unchecked {
          low = mid + 1;
        }
      } else {
        high = mid;
      }
    }

    return low;
  }

  /**
   * @dev Searches an `array` sorted in ascending order and returns the first
   * index that contains a value strictly greater than `element`. If no such index
   * exists (i.e. all values in the array are strictly less than `element`), the array
   * length is returned. Time complexity O(log n).
   *
   * See C++'s https://en.cppreference.com/w/cpp/algorithm/upper_bound[upper_bound].
   */
  function upperBound(uint256[] storage array, uint256 element) internal view returns (uint256) {
    uint256 low = 0;
    uint256 high = array.length;

    if (high == 0) {
      return 0;
    }

    while (low < high) {
      uint256 mid = Math.average(low, high);

      // Note that mid will always be strictly less than high (i.e. it will be a valid array index)
      // because Math.average rounds towards zero (it does integer division with truncation).
      if (unsafeAccess(array, mid).value > element) {
        high = mid;
      } else {
        // this cannot overflow because mid < high
        unchecked {
          low = mid + 1;
        }
      }
    }

    return low;
  }

  /**
   * @dev Same as {lowerBound}, but with an array in memory.
   */
  function lowerBoundMemory(
    uint256[] memory array,
    uint256 element
  ) internal pure returns (uint256) {
    uint256 low = 0;
    uint256 high = array.length;

    if (high == 0) {
      return 0;
    }

    while (low < high) {
      uint256 mid = Math.average(low, high);

      // Note that mid will always be strictly less than high (i.e. it will be a valid array index)
      // because Math.average rounds towards zero (it does integer division with truncation).
      if (unsafeMemoryAccess(array, mid) < element) {
        // this cannot overflow because mid < high
        unchecked {
          low = mid + 1;
        }
      } else {
        high = mid;
      }
    }

    return low;
  }

  /**
   * @dev Same as {upperBound}, but with an array in memory.
   */
  function upperBoundMemory(
    uint256[] memory array,
    uint256 element
  ) internal pure returns (uint256) {
    uint256 low = 0;
    uint256 high = array.length;

    if (high == 0) {
      return 0;
    }

    while (low < high) {
      uint256 mid = Math.average(low, high);

      // Note that mid will always be strictly less than high (i.e. it will be a valid array index)
      // because Math.average rounds towards zero (it does integer division with truncation).
      if (unsafeMemoryAccess(array, mid) > element) {
        high = mid;
      } else {
        // this cannot overflow because mid < high
        unchecked {
          low = mid + 1;
        }
      }
    }

    return low;
  }

  /**
   * @dev Copies the content of `array`, from `start` (included) to the end of `array` into a new address array in
   * memory.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(address[] memory array, uint256 start) internal pure returns (address[] memory) {
    return slice(array, start, array.length);
  }

  /**
   * @dev Copies the content of `array`, from `start` (included) to `end` (excluded) into a new address array in
   * memory. The `end` argument is truncated to the length of the `array`.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(
    address[] memory array,
    uint256 start,
    uint256 end
  ) internal pure returns (address[] memory) {
    // sanitize
    end = Math.min(end, array.length);
    start = Math.min(start, end);

    // allocate and copy
    address[] memory result = new address[](end - start);
    assembly ('memory-safe') {
      mcopy(add(result, 0x20), add(add(array, 0x20), mul(start, 0x20)), mul(sub(end, start), 0x20))
    }

    return result;
  }

  /**
   * @dev Copies the content of `array`, from `start` (included) to the end of `array` into a new bytes32 array in
   * memory.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(bytes32[] memory array, uint256 start) internal pure returns (bytes32[] memory) {
    return slice(array, start, array.length);
  }

  /**
   * @dev Copies the content of `array`, from `start` (included) to `end` (excluded) into a new bytes32 array in
   * memory. The `end` argument is truncated to the length of the `array`.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(
    bytes32[] memory array,
    uint256 start,
    uint256 end
  ) internal pure returns (bytes32[] memory) {
    // sanitize
    end = Math.min(end, array.length);
    start = Math.min(start, end);

    // allocate and copy
    bytes32[] memory result = new bytes32[](end - start);
    assembly ('memory-safe') {
      mcopy(add(result, 0x20), add(add(array, 0x20), mul(start, 0x20)), mul(sub(end, start), 0x20))
    }

    return result;
  }

  /**
   * @dev Copies the content of `array`, from `start` (included) to the end of `array` into a new uint256 array in
   * memory.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(uint256[] memory array, uint256 start) internal pure returns (uint256[] memory) {
    return slice(array, start, array.length);
  }

  /**
   * @dev Copies the content of `array`, from `start` (included) to `end` (excluded) into a new uint256 array in
   * memory. The `end` argument is truncated to the length of the `array`.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(
    uint256[] memory array,
    uint256 start,
    uint256 end
  ) internal pure returns (uint256[] memory) {
    // sanitize
    end = Math.min(end, array.length);
    start = Math.min(start, end);

    // allocate and copy
    uint256[] memory result = new uint256[](end - start);
    assembly ('memory-safe') {
      mcopy(add(result, 0x20), add(add(array, 0x20), mul(start, 0x20)), mul(sub(end, start), 0x20))
    }

    return result;
  }

  /**
   * @dev Moves the content of `array`, from `start` (included) to the end of `array` to the start of that array.
   *
   * NOTE: This function modifies the provided array in place. If you need to preserve the original array, use {slice} instead.
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(address[] memory array, uint256 start) internal pure returns (address[] memory) {
    return splice(array, start, array.length);
  }

  /**
   * @dev Moves the content of `array`, from `start` (included) to `end` (excluded) to the start of that array. The
   * `end` argument is truncated to the length of the `array`.
   *
   * NOTE: This function modifies the provided array in place. If you need to preserve the original array, use {slice} instead.
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(
    address[] memory array,
    uint256 start,
    uint256 end
  ) internal pure returns (address[] memory) {
    // sanitize
    end = Math.min(end, array.length);
    start = Math.min(start, end);

    // move and resize
    assembly ('memory-safe') {
      mcopy(add(array, 0x20), add(add(array, 0x20), mul(start, 0x20)), mul(sub(end, start), 0x20))
      mstore(array, sub(end, start))
    }

    return array;
  }

  /**
   * @dev Moves the content of `array`, from `start` (included) to the end of `array` to the start of that array.
   *
   * NOTE: This function modifies the provided array in place. If you need to preserve the original array, use {slice} instead.
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(bytes32[] memory array, uint256 start) internal pure returns (bytes32[] memory) {
    return splice(array, start, array.length);
  }

  /**
   * @dev Moves the content of `array`, from `start` (included) to `end` (excluded) to the start of that array. The
   * `end` argument is truncated to the length of the `array`.
   *
   * NOTE: This function modifies the provided array in place. If you need to preserve the original array, use {slice} instead.
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(
    bytes32[] memory array,
    uint256 start,
    uint256 end
  ) internal pure returns (bytes32[] memory) {
    // sanitize
    end = Math.min(end, array.length);
    start = Math.min(start, end);

    // move and resize
    assembly ('memory-safe') {
      mcopy(add(array, 0x20), add(add(array, 0x20), mul(start, 0x20)), mul(sub(end, start), 0x20))
      mstore(array, sub(end, start))
    }

    return array;
  }

  /**
   * @dev Moves the content of `array`, from `start` (included) to the end of `array` to the start of that array.
   *
   * NOTE: This function modifies the provided array in place. If you need to preserve the original array, use {slice} instead.
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(uint256[] memory array, uint256 start) internal pure returns (uint256[] memory) {
    return splice(array, start, array.length);
  }

  /**
   * @dev Moves the content of `array`, from `start` (included) to `end` (excluded) to the start of that array. The
   * `end` argument is truncated to the length of the `array`.
   *
   * NOTE: This function modifies the provided array in place. If you need to preserve the original array, use {slice} instead.
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(
    uint256[] memory array,
    uint256 start,
    uint256 end
  ) internal pure returns (uint256[] memory) {
    // sanitize
    end = Math.min(end, array.length);
    start = Math.min(start, end);

    // move and resize
    assembly ('memory-safe') {
      mcopy(add(array, 0x20), add(add(array, 0x20), mul(start, 0x20)), mul(sub(end, start), 0x20))
      mstore(array, sub(end, start))
    }

    return array;
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeAccess(
    address[] storage arr,
    uint256 pos
  ) internal pure returns (StorageSlot.AddressSlot storage) {
    bytes32 slot;
    assembly ('memory-safe') {
      slot := arr.slot
    }
    return slot.deriveArray().offset(pos).getAddressSlot();
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeAccess(
    bytes32[] storage arr,
    uint256 pos
  ) internal pure returns (StorageSlot.Bytes32Slot storage) {
    bytes32 slot;
    assembly ('memory-safe') {
      slot := arr.slot
    }
    return slot.deriveArray().offset(pos).getBytes32Slot();
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeAccess(
    uint256[] storage arr,
    uint256 pos
  ) internal pure returns (StorageSlot.Uint256Slot storage) {
    bytes32 slot;
    assembly ('memory-safe') {
      slot := arr.slot
    }
    return slot.deriveArray().offset(pos).getUint256Slot();
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeAccess(
    bytes[] storage arr,
    uint256 pos
  ) internal pure returns (StorageSlot.BytesSlot storage) {
    bytes32 slot;
    assembly ('memory-safe') {
      slot := arr.slot
    }
    return slot.deriveArray().offset(pos).getBytesSlot();
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeAccess(
    string[] storage arr,
    uint256 pos
  ) internal pure returns (StorageSlot.StringSlot storage) {
    bytes32 slot;
    assembly ('memory-safe') {
      slot := arr.slot
    }
    return slot.deriveArray().offset(pos).getStringSlot();
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeMemoryAccess(
    address[] memory arr,
    uint256 pos
  ) internal pure returns (address res) {
    assembly {
      res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
    }
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeMemoryAccess(
    bytes32[] memory arr,
    uint256 pos
  ) internal pure returns (bytes32 res) {
    assembly {
      res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
    }
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeMemoryAccess(
    uint256[] memory arr,
    uint256 pos
  ) internal pure returns (uint256 res) {
    assembly {
      res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
    }
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeMemoryAccess(
    bytes[] memory arr,
    uint256 pos
  ) internal pure returns (bytes memory res) {
    assembly {
      res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
    }
  }

  /**
   * @dev Access an array in an "unsafe" way. Skips solidity "index-out-of-range" check.
   *
   * WARNING: Only use if you are certain `pos` is lower than the array length.
   */
  function unsafeMemoryAccess(
    string[] memory arr,
    uint256 pos
  ) internal pure returns (string memory res) {
    assembly {
      res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
    }
  }

  /**
   * @dev Helper to set the length of a dynamic array. Directly writing to `.length` is forbidden.
   *
   * WARNING: this does not clear elements if length is reduced, of initialize elements if length is increased.
   */
  function unsafeSetLength(address[] storage array, uint256 len) internal {
    assembly ('memory-safe') {
      sstore(array.slot, len)
    }
  }

  /**
   * @dev Helper to set the length of a dynamic array. Directly writing to `.length` is forbidden.
   *
   * WARNING: this does not clear elements if length is reduced, of initialize elements if length is increased.
   */
  function unsafeSetLength(bytes32[] storage array, uint256 len) internal {
    assembly ('memory-safe') {
      sstore(array.slot, len)
    }
  }

  /**
   * @dev Helper to set the length of a dynamic array. Directly writing to `.length` is forbidden.
   *
   * WARNING: this does not clear elements if length is reduced, of initialize elements if length is increased.
   */
  function unsafeSetLength(uint256[] storage array, uint256 len) internal {
    assembly ('memory-safe') {
      sstore(array.slot, len)
    }
  }

  /**
   * @dev Helper to set the length of a dynamic array. Directly writing to `.length` is forbidden.
   *
   * WARNING: this does not clear elements if length is reduced, of initialize elements if length is increased.
   */
  function unsafeSetLength(bytes[] storage array, uint256 len) internal {
    assembly ('memory-safe') {
      sstore(array.slot, len)
    }
  }

  /**
   * @dev Helper to set the length of a dynamic array. Directly writing to `.length` is forbidden.
   *
   * WARNING: this does not clear elements if length is reduced, of initialize elements if length is increased.
   */
  function unsafeSetLength(string[] storage array, uint256 len) internal {
    assembly ('memory-safe') {
      sstore(array.slot, len)
    }
  }
}

// tests/helpers/mocks/TestnetERC20.sol

/**
 * @title TestnetERC20
 * @dev ERC20 minting logic
 */
contract TestnetERC20 is IERC20Permit, ERC20 {
  bytes public constant EIP712_REVISION = bytes('1');
  bytes32 internal constant EIP712_DOMAIN =
    keccak256('EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)');
  bytes32 public constant PERMIT_TYPEHASH =
    keccak256('Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)');

  // Map of address nonces (address => nonce)
  mapping(address => uint256) internal _nonces;

  bytes32 public DOMAIN_SEPARATOR;

  uint8 private _decimals;

  constructor(string memory name_, string memory symbol_, uint8 decimals_) ERC20(name_, symbol_) {
    uint256 chainId = block.chainid;

    DOMAIN_SEPARATOR = keccak256(
      abi.encode(
        EIP712_DOMAIN,
        keccak256(bytes(name_)),
        keccak256(EIP712_REVISION),
        chainId,
        address(this)
      )
    );
    _setupDecimals(decimals_);
  }

  /// @inheritdoc IERC20Permit
  function permit(
    address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) external override {
    require(owner != address(0), 'INVALID_OWNER');
    //solium-disable-next-line
    require(block.timestamp <= deadline, 'INVALID_EXPIRATION');
    uint256 currentValidNonce = _nonces[owner];
    bytes32 digest = keccak256(
      abi.encodePacked(
        '\x19\x01',
        DOMAIN_SEPARATOR,
        keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, currentValidNonce, deadline))
      )
    );
    require(owner == ecrecover(digest, v, r, s), 'INVALID_SIGNATURE');
    _nonces[owner] = currentValidNonce + 1;
    _approve(owner, spender, value);
  }

  /**
   * @dev Function to mint tokens
   * @param value The amount of tokens to mint.
   * @return A boolean that indicates if the operation was successful.
   */
  function mint(uint256 value) public virtual returns (bool) {
    _mint(_msgSender(), value);
    return true;
  }

  /**
   * @dev Function to mint tokens to address
   * @param account The account to mint tokens.
   * @param value The amount of tokens to mint.
   * @return A boolean that indicates if the operation was successful.
   */
  function mint(address account, uint256 value) public virtual returns (bool) {
    _mint(account, value);
    return true;
  }

  function nonces(address owner) public view returns (uint256) {
    return _nonces[owner];
  }

  function decimals() public view virtual override returns (uint8) {
    return _decimals;
  }

  /**
   * @dev Sets {decimals} to a value other than the default one of 18.
   *
   * WARNING: This function should only be called from the constructor. Most
   * applications that interact with token contracts will not expect
   * {decimals} to ever change, and may work incorrectly if it does.
   */
  function _setupDecimals(uint8 decimals_) internal {
    _decimals = decimals_;
  }
}

// src/dependencies/openzeppelin/EnumerableSet.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/structs/EnumerableSet.sol)
// This file was procedurally generated from scripts/generate/templates/EnumerableSet.js.

/**
 * @dev Library for managing
 * https://en.wikipedia.org/wiki/Set_(abstract_data_type)[sets] of primitive
 * types.
 *
 * Sets have the following properties:
 *
 * - Elements are added, removed, and checked for existence in constant time
 * (O(1)).
 * - Elements are enumerated in O(n). No guarantees are made on the ordering.
 * - Set can be cleared (all elements removed) in O(n).
 *
 * ```solidity
 * contract Example {
 *     // Add the library methods
 *     using EnumerableSet for EnumerableSet.AddressSet;
 *
 *     // Declare a set state variable
 *     EnumerableSet.AddressSet private mySet;
 * }
 * ```
 *
 * The following types are supported:
 *
 * - `bytes32` (`Bytes32Set`) since v3.3.0
 * - `address` (`AddressSet`) since v3.3.0
 * - `uint256` (`UintSet`) since v3.3.0
 * - `string` (`StringSet`) since v5.4.0
 * - `bytes` (`BytesSet`) since v5.4.0
 *
 * [WARNING]
 * ====
 * Trying to delete such a structure from storage will likely result in data corruption, rendering the structure
 * unusable.
 * See https://github.com/ethereum/solidity/pull/11843[ethereum/solidity#11843] for more info.
 *
 * In order to clean an EnumerableSet, you can either remove all elements one by one or create a fresh instance using an
 * array of EnumerableSet.
 * ====
 */
library EnumerableSet {
  // To implement this library for multiple types with as little code
  // repetition as possible, we write it in terms of a generic Set type with
  // bytes32 values.
  // The Set implementation uses private functions, and user-facing
  // implementations (such as AddressSet) are just wrappers around the
  // underlying Set.
  // This means that we can only create new EnumerableSets for types that fit
  // in bytes32.

  struct Set {
    // Storage of set values
    bytes32[] _values;
    // Position is the index of the value in the `values` array plus 1.
    // Position 0 is used to mean a value is not in the set.
    mapping(bytes32 value => uint256) _positions;
  }

  /**
   * @dev Add a value to a set. O(1).
   *
   * Returns true if the value was added to the set, that is if it was not
   * already present.
   */
  function _add(Set storage set, bytes32 value) private returns (bool) {
    if (!_contains(set, value)) {
      set._values.push(value);
      // The value is stored at length-1, but we add 1 to all indexes
      // and use 0 as a sentinel value
      set._positions[value] = set._values.length;
      return true;
    } else {
      return false;
    }
  }

  /**
   * @dev Removes a value from a set. O(1).
   *
   * Returns true if the value was removed from the set, that is if it was
   * present.
   */
  function _remove(Set storage set, bytes32 value) private returns (bool) {
    // We cache the value's position to prevent multiple reads from the same storage slot
    uint256 position = set._positions[value];

    if (position != 0) {
      // Equivalent to contains(set, value)
      // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
      // the array, and then remove the last element (sometimes called as 'swap and pop').
      // This modifies the order of the array, as noted in {at}.

      uint256 valueIndex = position - 1;
      uint256 lastIndex = set._values.length - 1;

      if (valueIndex != lastIndex) {
        bytes32 lastValue = set._values[lastIndex];

        // Move the lastValue to the index where the value to delete is
        set._values[valueIndex] = lastValue;
        // Update the tracked position of the lastValue (that was just moved)
        set._positions[lastValue] = position;
      }

      // Delete the slot where the moved value was stored
      set._values.pop();

      // Delete the tracked position for the deleted slot
      delete set._positions[value];

      return true;
    } else {
      return false;
    }
  }

  /**
   * @dev Removes all the values from a set. O(n).
   *
   * WARNING: This function has an unbounded cost that scales with set size. Developers should keep in mind that
   * using it may render the function uncallable if the set grows to the point where clearing it consumes too much
   * gas to fit in a block.
   */
  function _clear(Set storage set) private {
    uint256 len = _length(set);
    for (uint256 i = 0; i < len; ++i) {
      delete set._positions[set._values[i]];
    }
    Arrays.unsafeSetLength(set._values, 0);
  }

  /**
   * @dev Returns true if the value is in the set. O(1).
   */
  function _contains(Set storage set, bytes32 value) private view returns (bool) {
    return set._positions[value] != 0;
  }

  /**
   * @dev Returns the number of values on the set. O(1).
   */
  function _length(Set storage set) private view returns (uint256) {
    return set._values.length;
  }

  /**
   * @dev Returns the value stored at position `index` in the set. O(1).
   *
   * Note that there are no guarantees on the ordering of values inside the
   * array, and it may change when more values are added or removed.
   *
   * Requirements:
   *
   * - `index` must be strictly less than {length}.
   */
  function _at(Set storage set, uint256 index) private view returns (bytes32) {
    return set._values[index];
  }

  /**
   * @dev Return the entire set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function _values(Set storage set) private view returns (bytes32[] memory) {
    return set._values;
  }

  /**
   * @dev Return a slice of the set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function _values(
    Set storage set,
    uint256 start,
    uint256 end
  ) private view returns (bytes32[] memory) {
    unchecked {
      end = Math.min(end, _length(set));
      start = Math.min(start, end);

      uint256 len = end - start;
      bytes32[] memory result = new bytes32[](len);
      for (uint256 i = 0; i < len; ++i) {
        result[i] = Arrays.unsafeAccess(set._values, start + i).value;
      }
      return result;
    }
  }

  // Bytes32Set

  struct Bytes32Set {
    Set _inner;
  }

  /**
   * @dev Add a value to a set. O(1).
   *
   * Returns true if the value was added to the set, that is if it was not
   * already present.
   */
  function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
    return _add(set._inner, value);
  }

  /**
   * @dev Removes a value from a set. O(1).
   *
   * Returns true if the value was removed from the set, that is if it was
   * present.
   */
  function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
    return _remove(set._inner, value);
  }

  /**
   * @dev Removes all the values from a set. O(n).
   *
   * WARNING: Developers should keep in mind that this function has an unbounded cost and using it may render the
   * function uncallable if the set grows to the point where clearing it consumes too much gas to fit in a block.
   */
  function clear(Bytes32Set storage set) internal {
    _clear(set._inner);
  }

  /**
   * @dev Returns true if the value is in the set. O(1).
   */
  function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
    return _contains(set._inner, value);
  }

  /**
   * @dev Returns the number of values in the set. O(1).
   */
  function length(Bytes32Set storage set) internal view returns (uint256) {
    return _length(set._inner);
  }

  /**
   * @dev Returns the value stored at position `index` in the set. O(1).
   *
   * Note that there are no guarantees on the ordering of values inside the
   * array, and it may change when more values are added or removed.
   *
   * Requirements:
   *
   * - `index` must be strictly less than {length}.
   */
  function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
    return _at(set._inner, index);
  }

  /**
   * @dev Return the entire set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(Bytes32Set storage set) internal view returns (bytes32[] memory) {
    bytes32[] memory store = _values(set._inner);
    bytes32[] memory result;

    assembly ('memory-safe') {
      result := store
    }

    return result;
  }

  /**
   * @dev Return a slice of the set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(
    Bytes32Set storage set,
    uint256 start,
    uint256 end
  ) internal view returns (bytes32[] memory) {
    bytes32[] memory store = _values(set._inner, start, end);
    bytes32[] memory result;

    assembly ('memory-safe') {
      result := store
    }

    return result;
  }

  // AddressSet

  struct AddressSet {
    Set _inner;
  }

  /**
   * @dev Add a value to a set. O(1).
   *
   * Returns true if the value was added to the set, that is if it was not
   * already present.
   */
  function add(AddressSet storage set, address value) internal returns (bool) {
    return _add(set._inner, bytes32(uint256(uint160(value))));
  }

  /**
   * @dev Removes a value from a set. O(1).
   *
   * Returns true if the value was removed from the set, that is if it was
   * present.
   */
  function remove(AddressSet storage set, address value) internal returns (bool) {
    return _remove(set._inner, bytes32(uint256(uint160(value))));
  }

  /**
   * @dev Removes all the values from a set. O(n).
   *
   * WARNING: Developers should keep in mind that this function has an unbounded cost and using it may render the
   * function uncallable if the set grows to the point where clearing it consumes too much gas to fit in a block.
   */
  function clear(AddressSet storage set) internal {
    _clear(set._inner);
  }

  /**
   * @dev Returns true if the value is in the set. O(1).
   */
  function contains(AddressSet storage set, address value) internal view returns (bool) {
    return _contains(set._inner, bytes32(uint256(uint160(value))));
  }

  /**
   * @dev Returns the number of values in the set. O(1).
   */
  function length(AddressSet storage set) internal view returns (uint256) {
    return _length(set._inner);
  }

  /**
   * @dev Returns the value stored at position `index` in the set. O(1).
   *
   * Note that there are no guarantees on the ordering of values inside the
   * array, and it may change when more values are added or removed.
   *
   * Requirements:
   *
   * - `index` must be strictly less than {length}.
   */
  function at(AddressSet storage set, uint256 index) internal view returns (address) {
    return address(uint160(uint256(_at(set._inner, index))));
  }

  /**
   * @dev Return the entire set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(AddressSet storage set) internal view returns (address[] memory) {
    bytes32[] memory store = _values(set._inner);
    address[] memory result;

    assembly ('memory-safe') {
      result := store
    }

    return result;
  }

  /**
   * @dev Return a slice of the set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(
    AddressSet storage set,
    uint256 start,
    uint256 end
  ) internal view returns (address[] memory) {
    bytes32[] memory store = _values(set._inner, start, end);
    address[] memory result;

    assembly ('memory-safe') {
      result := store
    }

    return result;
  }

  // UintSet

  struct UintSet {
    Set _inner;
  }

  /**
   * @dev Add a value to a set. O(1).
   *
   * Returns true if the value was added to the set, that is if it was not
   * already present.
   */
  function add(UintSet storage set, uint256 value) internal returns (bool) {
    return _add(set._inner, bytes32(value));
  }

  /**
   * @dev Removes a value from a set. O(1).
   *
   * Returns true if the value was removed from the set, that is if it was
   * present.
   */
  function remove(UintSet storage set, uint256 value) internal returns (bool) {
    return _remove(set._inner, bytes32(value));
  }

  /**
   * @dev Removes all the values from a set. O(n).
   *
   * WARNING: Developers should keep in mind that this function has an unbounded cost and using it may render the
   * function uncallable if the set grows to the point where clearing it consumes too much gas to fit in a block.
   */
  function clear(UintSet storage set) internal {
    _clear(set._inner);
  }

  /**
   * @dev Returns true if the value is in the set. O(1).
   */
  function contains(UintSet storage set, uint256 value) internal view returns (bool) {
    return _contains(set._inner, bytes32(value));
  }

  /**
   * @dev Returns the number of values in the set. O(1).
   */
  function length(UintSet storage set) internal view returns (uint256) {
    return _length(set._inner);
  }

  /**
   * @dev Returns the value stored at position `index` in the set. O(1).
   *
   * Note that there are no guarantees on the ordering of values inside the
   * array, and it may change when more values are added or removed.
   *
   * Requirements:
   *
   * - `index` must be strictly less than {length}.
   */
  function at(UintSet storage set, uint256 index) internal view returns (uint256) {
    return uint256(_at(set._inner, index));
  }

  /**
   * @dev Return the entire set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(UintSet storage set) internal view returns (uint256[] memory) {
    bytes32[] memory store = _values(set._inner);
    uint256[] memory result;

    assembly ('memory-safe') {
      result := store
    }

    return result;
  }

  /**
   * @dev Return a slice of the set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(
    UintSet storage set,
    uint256 start,
    uint256 end
  ) internal view returns (uint256[] memory) {
    bytes32[] memory store = _values(set._inner, start, end);
    uint256[] memory result;

    assembly ('memory-safe') {
      result := store
    }

    return result;
  }

  struct StringSet {
    // Storage of set values
    string[] _values;
    // Position is the index of the value in the `values` array plus 1.
    // Position 0 is used to mean a value is not in the set.
    mapping(string value => uint256) _positions;
  }

  /**
   * @dev Add a value to a set. O(1).
   *
   * Returns true if the value was added to the set, that is if it was not
   * already present.
   */
  function add(StringSet storage set, string memory value) internal returns (bool) {
    if (!contains(set, value)) {
      set._values.push(value);
      // The value is stored at length-1, but we add 1 to all indexes
      // and use 0 as a sentinel value
      set._positions[value] = set._values.length;
      return true;
    } else {
      return false;
    }
  }

  /**
   * @dev Removes a value from a set. O(1).
   *
   * Returns true if the value was removed from the set, that is if it was
   * present.
   */
  function remove(StringSet storage set, string memory value) internal returns (bool) {
    // We cache the value's position to prevent multiple reads from the same storage slot
    uint256 position = set._positions[value];

    if (position != 0) {
      // Equivalent to contains(set, value)
      // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
      // the array, and then remove the last element (sometimes called as 'swap and pop').
      // This modifies the order of the array, as noted in {at}.

      uint256 valueIndex = position - 1;
      uint256 lastIndex = set._values.length - 1;

      if (valueIndex != lastIndex) {
        string memory lastValue = set._values[lastIndex];

        // Move the lastValue to the index where the value to delete is
        set._values[valueIndex] = lastValue;
        // Update the tracked position of the lastValue (that was just moved)
        set._positions[lastValue] = position;
      }

      // Delete the slot where the moved value was stored
      set._values.pop();

      // Delete the tracked position for the deleted slot
      delete set._positions[value];

      return true;
    } else {
      return false;
    }
  }

  /**
   * @dev Removes all the values from a set. O(n).
   *
   * WARNING: Developers should keep in mind that this function has an unbounded cost and using it may render the
   * function uncallable if the set grows to the point where clearing it consumes too much gas to fit in a block.
   */
  function clear(StringSet storage set) internal {
    uint256 len = length(set);
    for (uint256 i = 0; i < len; ++i) {
      delete set._positions[set._values[i]];
    }
    Arrays.unsafeSetLength(set._values, 0);
  }

  /**
   * @dev Returns true if the value is in the set. O(1).
   */
  function contains(StringSet storage set, string memory value) internal view returns (bool) {
    return set._positions[value] != 0;
  }

  /**
   * @dev Returns the number of values on the set. O(1).
   */
  function length(StringSet storage set) internal view returns (uint256) {
    return set._values.length;
  }

  /**
   * @dev Returns the value stored at position `index` in the set. O(1).
   *
   * Note that there are no guarantees on the ordering of values inside the
   * array, and it may change when more values are added or removed.
   *
   * Requirements:
   *
   * - `index` must be strictly less than {length}.
   */
  function at(StringSet storage set, uint256 index) internal view returns (string memory) {
    return set._values[index];
  }

  /**
   * @dev Return the entire set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(StringSet storage set) internal view returns (string[] memory) {
    return set._values;
  }

  /**
   * @dev Return a slice of the set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(
    StringSet storage set,
    uint256 start,
    uint256 end
  ) internal view returns (string[] memory) {
    unchecked {
      end = Math.min(end, length(set));
      start = Math.min(start, end);

      uint256 len = end - start;
      string[] memory result = new string[](len);
      for (uint256 i = 0; i < len; ++i) {
        result[i] = Arrays.unsafeAccess(set._values, start + i).value;
      }
      return result;
    }
  }

  struct BytesSet {
    // Storage of set values
    bytes[] _values;
    // Position is the index of the value in the `values` array plus 1.
    // Position 0 is used to mean a value is not in the set.
    mapping(bytes value => uint256) _positions;
  }

  /**
   * @dev Add a value to a set. O(1).
   *
   * Returns true if the value was added to the set, that is if it was not
   * already present.
   */
  function add(BytesSet storage set, bytes memory value) internal returns (bool) {
    if (!contains(set, value)) {
      set._values.push(value);
      // The value is stored at length-1, but we add 1 to all indexes
      // and use 0 as a sentinel value
      set._positions[value] = set._values.length;
      return true;
    } else {
      return false;
    }
  }

  /**
   * @dev Removes a value from a set. O(1).
   *
   * Returns true if the value was removed from the set, that is if it was
   * present.
   */
  function remove(BytesSet storage set, bytes memory value) internal returns (bool) {
    // We cache the value's position to prevent multiple reads from the same storage slot
    uint256 position = set._positions[value];

    if (position != 0) {
      // Equivalent to contains(set, value)
      // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
      // the array, and then remove the last element (sometimes called as 'swap and pop').
      // This modifies the order of the array, as noted in {at}.

      uint256 valueIndex = position - 1;
      uint256 lastIndex = set._values.length - 1;

      if (valueIndex != lastIndex) {
        bytes memory lastValue = set._values[lastIndex];

        // Move the lastValue to the index where the value to delete is
        set._values[valueIndex] = lastValue;
        // Update the tracked position of the lastValue (that was just moved)
        set._positions[lastValue] = position;
      }

      // Delete the slot where the moved value was stored
      set._values.pop();

      // Delete the tracked position for the deleted slot
      delete set._positions[value];

      return true;
    } else {
      return false;
    }
  }

  /**
   * @dev Removes all the values from a set. O(n).
   *
   * WARNING: Developers should keep in mind that this function has an unbounded cost and using it may render the
   * function uncallable if the set grows to the point where clearing it consumes too much gas to fit in a block.
   */
  function clear(BytesSet storage set) internal {
    uint256 len = length(set);
    for (uint256 i = 0; i < len; ++i) {
      delete set._positions[set._values[i]];
    }
    Arrays.unsafeSetLength(set._values, 0);
  }

  /**
   * @dev Returns true if the value is in the set. O(1).
   */
  function contains(BytesSet storage set, bytes memory value) internal view returns (bool) {
    return set._positions[value] != 0;
  }

  /**
   * @dev Returns the number of values on the set. O(1).
   */
  function length(BytesSet storage set) internal view returns (uint256) {
    return set._values.length;
  }

  /**
   * @dev Returns the value stored at position `index` in the set. O(1).
   *
   * Note that there are no guarantees on the ordering of values inside the
   * array, and it may change when more values are added or removed.
   *
   * Requirements:
   *
   * - `index` must be strictly less than {length}.
   */
  function at(BytesSet storage set, uint256 index) internal view returns (bytes memory) {
    return set._values[index];
  }

  /**
   * @dev Return the entire set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(BytesSet storage set) internal view returns (bytes[] memory) {
    return set._values;
  }

  /**
   * @dev Return a slice of the set in an array
   *
   * WARNING: This operation will copy the entire storage to memory, which can be quite expensive. This is designed
   * to mostly be used by view accessors that are queried without any gas fees. Developers should keep in mind that
   * this function has an unbounded cost, and using it as part of a state-changing function may render the function
   * uncallable if the set grows to a point where copying to memory consumes too much gas to fit in a block.
   */
  function values(
    BytesSet storage set,
    uint256 start,
    uint256 end
  ) internal view returns (bytes[] memory) {
    unchecked {
      end = Math.min(end, length(set));
      start = Math.min(start, end);

      uint256 len = end - start;
      bytes[] memory result = new bytes[](len);
      for (uint256 i = 0; i < len; ++i) {
        result[i] = Arrays.unsafeAccess(set._values, start + i).value;
      }
      return result;
    }
  }
}

// src/hub/HubStorage.sol

/// @title HubStorage
/// @author Aave Labs
/// @notice Storage layout for the Hub contract.
/// @dev This contract defines all storage variables used by the Hub.
abstract contract HubStorage {
  /// @dev Number of assets listed in the Hub.
  uint256 internal _assetCount;

  /// @dev Map of asset identifiers to Asset data.
  mapping(uint256 assetId => IHub.Asset) internal _assets;

  /// @dev Map of asset identifiers and spoke addresses to Spoke data.
  mapping(uint256 assetId => mapping(address spoke => IHub.SpokeData)) internal _spokes;

  /// @dev Map of asset identifiers to set of spoke addresses.
  mapping(uint256 assetId => EnumerableSet.AddressSet) internal _assetToSpokes;

  /// @dev Map of underlying addresses to asset identifiers.
  mapping(address underlying => uint256 assetId) internal _underlyingToAssetId;

  /// @dev Reserved storage space to allow for future layout updates.
  uint256[50] private __gap;
}

// src/hub/libraries/AssetLogic.sol

/// @title AssetLogic library
/// @author Aave Labs
/// @notice Implements the base logic and share price conversions for asset data.
library AssetLogic {
  using AssetLogic for IHub.Asset;
  using SafeCast for uint256;
  using MathUtils for uint256;
  using PercentageMath for uint256;
  using WadRayMath for *;
  using SharesMath for uint256;

  /// @notice Converts an amount of shares to the equivalent amount of drawn assets, rounding up.
  function toDrawnAssetsUp(
    IHub.Asset storage asset,
    uint256 shares
  ) internal view returns (uint256) {
    return shares.rayMulUp(asset.getDrawnIndex());
  }

  /// @notice Converts an amount of shares to the equivalent amount of drawn assets, rounding down.
  function toDrawnAssetsDown(
    IHub.Asset storage asset,
    uint256 shares
  ) internal view returns (uint256) {
    return shares.rayMulDown(asset.getDrawnIndex());
  }

  /// @notice Converts an amount of drawn assets to the equivalent amount of shares, rounding up.
  function toDrawnSharesUp(
    IHub.Asset storage asset,
    uint256 assets
  ) internal view returns (uint256) {
    return assets.rayDivUp(asset.getDrawnIndex());
  }

  /// @notice Converts an amount of drawn assets to the equivalent amount of shares, rounding down.
  function toDrawnSharesDown(
    IHub.Asset storage asset,
    uint256 assets
  ) internal view returns (uint256) {
    return assets.rayDivDown(asset.getDrawnIndex());
  }

  /// @notice Returns the total drawn assets amount for the specified asset.
  function drawn(IHub.Asset storage asset, uint256 drawnIndex) internal view returns (uint256) {
    return asset.drawnShares.rayMulUp(drawnIndex);
  }

  /// @notice Returns the total premium amount for the specified asset.
  function premium(IHub.Asset storage asset, uint256 drawnIndex) internal view returns (uint256) {
    return
      Premium
        .calculatePremiumRay({
          premiumShares: asset.premiumShares,
          drawnIndex: drawnIndex,
          premiumOffsetRay: asset.premiumOffsetRay
        })
        .fromRayUp();
  }

  /// @notice Returns the total amount owed for the specified asset, including drawn and premium.
  function totalOwed(IHub.Asset storage asset, uint256 drawnIndex) internal view returns (uint256) {
    return asset.drawn(drawnIndex) + asset.premium(drawnIndex);
  }

  /// @notice Returns the total added assets for the specified asset.
  function totalAddedAssets(IHub.Asset storage asset) internal view returns (uint256) {
    uint256 drawnIndex = asset.getDrawnIndex();

    uint256 aggregatedOwedRay = _calculateAggregatedOwedRay({
      drawnShares: asset.drawnShares,
      premiumShares: asset.premiumShares,
      premiumOffsetRay: asset.premiumOffsetRay,
      deficitRay: asset.deficitRay,
      drawnIndex: drawnIndex
    });

    return
      asset.liquidity +
      asset.swept +
      aggregatedOwedRay.fromRayUp() -
      asset.realizedFees -
      asset.getUnrealizedFees(drawnIndex);
  }

  /// @notice Converts an amount of shares to the equivalent amount of added assets, rounding up.
  function toAddedAssetsUp(
    IHub.Asset storage asset,
    uint256 shares
  ) internal view returns (uint256) {
    return shares.toAssetsUp(asset.totalAddedAssets(), asset.addedShares);
  }

  /// @notice Converts an amount of shares to the equivalent amount of added assets, rounding down.
  function toAddedAssetsDown(
    IHub.Asset storage asset,
    uint256 shares
  ) internal view returns (uint256) {
    return shares.toAssetsDown(asset.totalAddedAssets(), asset.addedShares);
  }

  /// @notice Converts an amount of added assets to the equivalent amount of shares, rounding up.
  function toAddedSharesUp(
    IHub.Asset storage asset,
    uint256 assets
  ) internal view returns (uint256) {
    return assets.toSharesUp(asset.totalAddedAssets(), asset.addedShares);
  }

  /// @notice Converts an amount of added assets to the equivalent amount of shares, rounding down.
  function toAddedSharesDown(
    IHub.Asset storage asset,
    uint256 assets
  ) internal view returns (uint256) {
    return assets.toSharesDown(asset.totalAddedAssets(), asset.addedShares);
  }

  /// @notice Updates the drawn rate of a specified asset.
  /// @dev Uses last stored index; asset accrual should have already occurred.
  function updateDrawnRate(IHub.Asset storage asset, uint256 assetId) internal {
    uint256 drawnIndex = asset.drawnIndex;
    uint256 newDrawnRate = asset.getDrawnRate(assetId, drawnIndex);
    asset.drawnRate = newDrawnRate.toUint96();

    emit IHub.UpdateAsset(assetId, drawnIndex, newDrawnRate, asset.realizedFees);
  }

  /// @notice Accrues interest and fees for the specified asset.
  function accrue(IHub.Asset storage asset) internal {
    if (asset.lastUpdateTimestamp == block.timestamp) {
      return;
    }

    uint256 drawnIndex = asset.getDrawnIndex();
    asset.realizedFees += asset.getUnrealizedFees(drawnIndex).toUint120();
    asset.drawnIndex = drawnIndex.toUint120();
    asset.lastUpdateTimestamp = block.timestamp.toUint40();
  }

  /// @notice Calculates the drawn index of a specified asset based on the existing drawn rate and index.
  function getDrawnIndex(IHub.Asset storage asset) internal view returns (uint256) {
    uint256 previousIndex = asset.drawnIndex;
    uint40 lastUpdateTimestamp = asset.lastUpdateTimestamp;
    if (
      lastUpdateTimestamp == block.timestamp || (asset.drawnShares == 0 && asset.premiumShares == 0)
    ) {
      return previousIndex;
    }
    return
      previousIndex.rayMulUp(
        MathUtils.calculateLinearInterest(asset.drawnRate, lastUpdateTimestamp)
      );
  }

  /// @notice Calculates the drawn rate of a specified asset using the specified drawn index.
  /// @dev Premium debt is not used in the interest rate calculation.
  /// @dev Imprecision from downscaling `deficitRay` does not accumulate.
  function getDrawnRate(
    IHub.Asset storage asset,
    uint256 assetId,
    uint256 drawnIndex
  ) internal view returns (uint256) {
    return
      IBasicInterestRateStrategy(asset.irStrategy).calculateInterestRate({
        assetId: assetId,
        liquidity: asset.liquidity,
        drawn: asset.drawn(drawnIndex),
        deficit: asset.deficitRay.fromRayUp(),
        swept: asset.swept
      });
  }

  /// @notice Calculates the amount of fees derived from the index growth due to interest accrual.
  /// @param drawnIndex The current drawn index.
  function getUnrealizedFees(
    IHub.Asset storage asset,
    uint256 drawnIndex
  ) internal view returns (uint256) {
    uint256 previousIndex = asset.drawnIndex;
    if (previousIndex == drawnIndex) {
      return 0;
    }

    uint256 liquidityFee = asset.liquidityFee;
    if (liquidityFee == 0) {
      return 0;
    }

    uint120 drawnShares = asset.drawnShares;
    uint120 premiumShares = asset.premiumShares;
    int256 premiumOffsetRay = asset.premiumOffsetRay;
    uint256 deficitRay = asset.deficitRay;

    uint256 aggregatedOwedRayAfter = _calculateAggregatedOwedRay({
      drawnShares: drawnShares,
      premiumShares: premiumShares,
      premiumOffsetRay: premiumOffsetRay,
      deficitRay: deficitRay,
      drawnIndex: drawnIndex
    });

    uint256 aggregatedOwedRayBefore = _calculateAggregatedOwedRay({
      drawnShares: drawnShares,
      premiumShares: premiumShares,
      premiumOffsetRay: premiumOffsetRay,
      deficitRay: deficitRay,
      drawnIndex: previousIndex
    });

    return
      (aggregatedOwedRayAfter.fromRayUp() - aggregatedOwedRayBefore.fromRayUp()).percentMulDown(
        liquidityFee
      );
  }

  /// @notice Calculates the aggregated owed amount for a specified asset, expressed in asset units and scaled by RAY.
  function _calculateAggregatedOwedRay(
    uint256 drawnShares,
    uint256 premiumShares,
    int256 premiumOffsetRay,
    uint256 deficitRay,
    uint256 drawnIndex
  ) internal pure returns (uint256) {
    uint256 premiumRay = Premium.calculatePremiumRay({
      premiumShares: premiumShares,
      premiumOffsetRay: premiumOffsetRay,
      drawnIndex: drawnIndex
    });
    return (drawnShares * drawnIndex) + premiumRay + deficitRay;
  }
}

// src/hub/Hub.sol

/// @title Hub
/// @author Aave Labs
/// @notice A liquidity hub that manages assets and spokes.
abstract contract Hub is IHub, HubStorage, AccessManagedUpgradeable {
  using EnumerableSet for EnumerableSet.AddressSet;
  using SafeCast for *;
  using SafeERC20 for IERC20;
  using MathUtils for *;
  using PercentageMath for *;
  using WadRayMath for uint256;
  using AssetLogic for Asset;
  using SharesMath for uint256;

  /// @inheritdoc IHub
  uint8 public constant MAX_ALLOWED_UNDERLYING_DECIMALS = 18;

  /// @inheritdoc IHub
  uint8 public constant MIN_ALLOWED_UNDERLYING_DECIMALS = 6;

  /// @inheritdoc IHub
  uint40 public constant MAX_ALLOWED_SPOKE_CAP = type(uint40).max;

  /// @inheritdoc IHub
  uint24 public constant MAX_RISK_PREMIUM_THRESHOLD = type(uint24).max;

  /// @dev To be overridden by the inheriting Hub instance contract.
  function initialize(address authority) external virtual;

  /// @inheritdoc IHub
  function addAsset(
    address underlying,
    uint8 decimals,
    address feeReceiver,
    address irStrategy,
    bytes calldata irData
  ) external restricted returns (uint256) {
    require(
      underlying != address(0) && feeReceiver != address(0) && irStrategy != address(0),
      InvalidAddress()
    );
    require(
      MIN_ALLOWED_UNDERLYING_DECIMALS <= decimals && decimals <= MAX_ALLOWED_UNDERLYING_DECIMALS,
      InvalidAssetDecimals()
    );
    require(!isUnderlyingListed(underlying), UnderlyingAlreadyListed());

    uint256 assetId = _assetCount++;
    _underlyingToAssetId[underlying] = assetId;

    IBasicInterestRateStrategy(irStrategy).setInterestRateData(assetId, irData);
    uint256 drawnRate = IBasicInterestRateStrategy(irStrategy).calculateInterestRate({
      assetId: assetId,
      liquidity: 0,
      drawn: 0,
      deficit: 0,
      swept: 0
    });

    uint256 drawnIndex = WadRayMath.RAY;
    uint256 lastUpdateTimestamp = block.timestamp;
    _assets[assetId] = Asset({
      liquidity: 0,
      deficitRay: 0,
      swept: 0,
      addedShares: 0,
      drawnShares: 0,
      premiumShares: 0,
      premiumOffsetRay: 0,
      drawnIndex: drawnIndex.toUint120(),
      underlying: underlying,
      lastUpdateTimestamp: lastUpdateTimestamp.toUint40(),
      decimals: decimals,
      drawnRate: drawnRate.toUint96(),
      irStrategy: irStrategy,
      realizedFees: 0,
      reinvestmentController: address(0),
      feeReceiver: feeReceiver,
      liquidityFee: 0
    });
    _addFeeReceiver(assetId, feeReceiver);

    emit AddAsset(assetId, underlying, decimals);
    emit UpdateAssetConfig(
      assetId,
      AssetConfig({
        feeReceiver: feeReceiver,
        liquidityFee: 0,
        irStrategy: irStrategy,
        reinvestmentController: address(0)
      })
    );
    emit UpdateAsset(assetId, drawnIndex, drawnRate, 0);

    return assetId;
  }

  /// @inheritdoc IHub
  function updateAssetConfig(
    uint256 assetId,
    AssetConfig calldata config,
    bytes calldata irData
  ) external restricted {
    require(assetId < _assetCount, AssetNotListed());
    Asset storage asset = _assets[assetId];
    asset.accrue();

    require(config.liquidityFee <= PercentageMath.PERCENTAGE_FACTOR, InvalidLiquidityFee());
    require(config.feeReceiver != address(0) && config.irStrategy != address(0), InvalidAddress());
    require(
      config.reinvestmentController != address(0) || asset.swept == 0,
      InvalidReinvestmentController()
    );

    asset.liquidityFee = config.liquidityFee;
    asset.reinvestmentController = config.reinvestmentController;

    address oldFeeReceiver = asset.feeReceiver;
    if (oldFeeReceiver != config.feeReceiver) {
      _mintFeeShares(asset, assetId);
      IHub.SpokeConfig memory spokeConfig;
      spokeConfig.active = _spokes[assetId][oldFeeReceiver].active;
      spokeConfig.halted = _spokes[assetId][oldFeeReceiver].halted;
      _updateSpokeConfig(assetId, oldFeeReceiver, spokeConfig);
      asset.feeReceiver = config.feeReceiver;
      _addFeeReceiver(assetId, config.feeReceiver);
    }

    if (config.irStrategy != asset.irStrategy) {
      asset.irStrategy = config.irStrategy;
      IBasicInterestRateStrategy(config.irStrategy).setInterestRateData(assetId, irData);
    } else {
      require(irData.length == 0, InvalidInterestRateStrategy());
    }

    asset.updateDrawnRate(assetId);

    emit UpdateAssetConfig(assetId, config);
  }

  /// @inheritdoc IHub
  function addSpoke(
    uint256 assetId,
    address spoke,
    SpokeConfig calldata config
  ) external restricted {
    require(assetId < _assetCount, AssetNotListed());
    require(spoke != address(0), InvalidAddress());
    _addSpoke(assetId, spoke);
    _updateSpokeConfig(assetId, spoke, config);
  }

  /// @inheritdoc IHub
  function updateSpokeConfig(
    uint256 assetId,
    address spoke,
    SpokeConfig calldata config
  ) external restricted {
    require(assetId < _assetCount, AssetNotListed());
    require(_assetToSpokes[assetId].contains(spoke), SpokeNotListed());
    _updateSpokeConfig(assetId, spoke, config);
  }

  /// @inheritdoc IHub
  function setInterestRateData(uint256 assetId, bytes calldata irData) external restricted {
    require(assetId < _assetCount, AssetNotListed());
    Asset storage asset = _assets[assetId];
    asset.accrue();
    IBasicInterestRateStrategy(asset.irStrategy).setInterestRateData(assetId, irData);
    asset.updateDrawnRate(assetId);
  }

  /// @inheritdoc IHub
  function mintFeeShares(uint256 assetId) external restricted returns (uint256) {
    require(assetId < _assetCount, AssetNotListed());
    Asset storage asset = _assets[assetId];
    asset.accrue();
    uint256 feeShares = _mintFeeShares(asset, assetId);
    asset.updateDrawnRate(assetId);
    return feeShares;
  }

  /// @inheritdoc IHubBase
  function add(uint256 assetId, uint256 amount) external returns (uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spoke = _spokes[assetId][msg.sender];

    asset.accrue();
    _validateAdd(asset, spoke, amount);

    uint256 liquidity = asset.liquidity + amount;
    uint256 balance = IERC20(asset.underlying).balanceOf(address(this));
    require(balance >= liquidity, InsufficientTransferred(liquidity.uncheckedSub(balance)));
    uint120 shares = asset.toAddedSharesDown(amount).toUint120();
    require(shares > 0, InvalidShares());
    asset.addedShares += shares;
    spoke.addedShares += shares;
    asset.liquidity = liquidity.toUint120();

    asset.updateDrawnRate(assetId);

    emit Add(assetId, msg.sender, shares, amount);

    return shares;
  }

  /// @inheritdoc IHubBase
  function remove(uint256 assetId, uint256 amount, address to) external returns (uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spoke = _spokes[assetId][msg.sender];

    asset.accrue();
    _validateRemove(spoke, amount, to);

    uint256 liquidity = asset.liquidity;
    require(amount <= liquidity, InsufficientLiquidity(liquidity));

    uint120 shares = asset.toAddedSharesUp(amount).toUint120();
    asset.addedShares -= shares;
    spoke.addedShares -= shares;
    asset.liquidity = liquidity.uncheckedSub(amount).toUint120();

    asset.updateDrawnRate(assetId);

    IERC20(asset.underlying).safeTransfer(to, amount);

    emit Remove(assetId, msg.sender, shares, amount);

    return shares;
  }

  /// @inheritdoc IHubBase
  function draw(uint256 assetId, uint256 amount, address to) external returns (uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spoke = _spokes[assetId][msg.sender];

    asset.accrue();
    _validateDraw(asset, spoke, amount, to);

    uint256 liquidity = asset.liquidity;
    require(amount <= liquidity, InsufficientLiquidity(liquidity));

    uint120 drawnShares = asset.toDrawnSharesUp(amount).toUint120();
    asset.drawnShares += drawnShares;
    spoke.drawnShares += drawnShares;
    asset.liquidity = liquidity.uncheckedSub(amount).toUint120();

    asset.updateDrawnRate(assetId);

    IERC20(asset.underlying).safeTransfer(to, amount);

    emit Draw(assetId, msg.sender, drawnShares, amount);

    return drawnShares;
  }

  /// @inheritdoc IHubBase
  function restore(
    uint256 assetId,
    uint256 drawnAmount,
    PremiumDelta calldata premiumDelta
  ) external returns (uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spoke = _spokes[assetId][msg.sender];

    asset.accrue();
    _validateRestore(asset, spoke, drawnAmount, premiumDelta.restoredPremiumRay);

    uint120 drawnShares = asset.toDrawnSharesDown(drawnAmount).toUint120();
    asset.drawnShares -= drawnShares;
    spoke.drawnShares -= drawnShares;
    _applyPremiumDelta(asset, spoke, premiumDelta);

    uint256 premiumAmount = premiumDelta.restoredPremiumRay.fromRayUp();
    uint256 liquidity = asset.liquidity + drawnAmount + premiumAmount;
    uint256 balance = IERC20(asset.underlying).balanceOf(address(this));
    require(balance >= liquidity, InsufficientTransferred(liquidity.uncheckedSub(balance)));
    asset.liquidity = liquidity.toUint120();

    asset.updateDrawnRate(assetId);

    emit Restore(assetId, msg.sender, drawnShares, premiumDelta, drawnAmount, premiumAmount);

    return drawnShares;
  }

  /// @inheritdoc IHubBase
  function reportDeficit(
    uint256 assetId,
    uint256 drawnAmount,
    PremiumDelta calldata premiumDelta
  ) external returns (uint256, uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spoke = _spokes[assetId][msg.sender];

    asset.accrue();
    _validateReportDeficit(asset, spoke, drawnAmount, premiumDelta.restoredPremiumRay);

    uint120 drawnShares = asset.toDrawnSharesDown(drawnAmount).toUint120();
    asset.drawnShares -= drawnShares;
    spoke.drawnShares -= drawnShares;
    _applyPremiumDelta(asset, spoke, premiumDelta);

    uint256 deficitAmountRay = uint256(drawnShares) * asset.drawnIndex +
      premiumDelta.restoredPremiumRay;
    asset.deficitRay += deficitAmountRay.toUint200();
    spoke.deficitRay += deficitAmountRay.toUint200();

    asset.updateDrawnRate(assetId);

    emit ReportDeficit(assetId, msg.sender, drawnShares, premiumDelta, deficitAmountRay);

    return (drawnShares, deficitAmountRay.fromRayUp());
  }

  /// @inheritdoc IHub
  function eliminateDeficit(
    uint256 assetId,
    uint256 amount,
    address spoke
  ) external restricted returns (uint256, uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage callerSpoke = _spokes[assetId][msg.sender];
    SpokeData storage coveredSpoke = _spokes[assetId][spoke];

    asset.accrue();
    uint256 deficitRay = coveredSpoke.deficitRay;
    uint256 deficitAmountRay = (amount < deficitRay.fromRayUp()) ? amount.toRay() : deficitRay;
    _validateEliminateDeficit(callerSpoke, deficitAmountRay);

    uint256 deficitToEliminate = deficitAmountRay.fromRayUp();
    uint120 shares = asset.toAddedSharesUp(deficitToEliminate).toUint120();
    asset.addedShares -= shares;
    callerSpoke.addedShares -= shares;
    asset.deficitRay -= deficitAmountRay.toUint200();
    coveredSpoke.deficitRay -= deficitAmountRay.toUint200();

    asset.updateDrawnRate(assetId);

    emit EliminateDeficit(assetId, msg.sender, spoke, shares, deficitAmountRay);

    return (shares, deficitToEliminate);
  }

  /// @inheritdoc IHubBase
  function refreshPremium(uint256 assetId, PremiumDelta calldata premiumDelta) external {
    Asset storage asset = _assets[assetId];
    SpokeData storage spoke = _spokes[assetId][msg.sender];

    asset.accrue();
    require(spoke.active, SpokeNotActive());
    // no premium change allowed
    require(premiumDelta.restoredPremiumRay == 0, InvalidPremiumChange());
    _applyPremiumDelta(asset, spoke, premiumDelta);
    asset.updateDrawnRate(assetId);

    emit RefreshPremium(assetId, msg.sender, premiumDelta);
  }

  /// @inheritdoc IHubBase
  function payFeeShares(uint256 assetId, uint256 shares) external {
    Asset storage asset = _assets[assetId];
    address feeReceiver = _assets[assetId].feeReceiver;
    SpokeData storage receiverSpoke = _spokes[assetId][feeReceiver];
    SpokeData storage callerSpoke = _spokes[assetId][msg.sender];

    asset.accrue();
    _validatePayFeeShares(callerSpoke, shares);
    _transferShares({sender: callerSpoke, receiver: receiverSpoke, shares: shares});
    asset.updateDrawnRate(assetId);

    emit TransferShares(assetId, msg.sender, feeReceiver, shares);
  }

  /// @inheritdoc IHub
  function transferShares(uint256 assetId, uint256 shares, address toSpoke) external {
    Asset storage asset = _assets[assetId];
    SpokeData storage callerSpoke = _spokes[assetId][msg.sender];
    SpokeData storage receiverSpoke = _spokes[assetId][toSpoke];

    asset.accrue();
    _validateTransferShares(asset, callerSpoke, receiverSpoke, shares);
    _transferShares({sender: callerSpoke, receiver: receiverSpoke, shares: shares});
    asset.updateDrawnRate(assetId);

    emit TransferShares(assetId, msg.sender, toSpoke, shares);
  }

  /// @inheritdoc IHub
  function sweep(uint256 assetId, uint256 amount) external {
    require(assetId < _assetCount, AssetNotListed());
    Asset storage asset = _assets[assetId];

    asset.accrue();
    _validateSweep(asset, msg.sender, amount);

    uint256 liquidity = asset.liquidity;
    require(amount <= liquidity, InsufficientLiquidity(liquidity));

    asset.liquidity = liquidity.uncheckedSub(amount).toUint120();
    asset.swept += amount.toUint120();

    asset.updateDrawnRate(assetId);

    IERC20(asset.underlying).safeTransfer(msg.sender, amount);

    emit Sweep(assetId, msg.sender, amount);
  }

  /// @inheritdoc IHub
  function reclaim(uint256 assetId, uint256 amount) external {
    require(assetId < _assetCount, AssetNotListed());
    Asset storage asset = _assets[assetId];

    asset.accrue();
    _validateReclaim(asset, msg.sender, amount);

    uint256 liquidity = asset.liquidity + amount;
    uint256 balance = IERC20(asset.underlying).balanceOf(address(this));
    require(balance >= liquidity, InsufficientTransferred(liquidity.uncheckedSub(balance)));
    asset.liquidity = liquidity.toUint120();
    asset.swept -= amount.toUint120();

    asset.updateDrawnRate(assetId);

    emit Reclaim(assetId, msg.sender, amount);
  }

  /// @inheritdoc IHub
  function isUnderlyingListed(address underlying) public view returns (bool) {
    return _assets[_underlyingToAssetId[underlying]].underlying == underlying;
  }

  /// @inheritdoc IHub
  function getAssetCount() external view returns (uint256) {
    return _assetCount;
  }

  /// @inheritdoc IHubBase
  function previewAddByAssets(uint256 assetId, uint256 assets) external view returns (uint256) {
    return _assets[assetId].toAddedSharesDown(assets);
  }

  /// @inheritdoc IHubBase
  function previewAddByShares(uint256 assetId, uint256 shares) external view returns (uint256) {
    return _assets[assetId].toAddedAssetsUp(shares);
  }

  /// @inheritdoc IHubBase
  function previewRemoveByAssets(uint256 assetId, uint256 assets) external view returns (uint256) {
    return _assets[assetId].toAddedSharesUp(assets);
  }

  /// @inheritdoc IHubBase
  function previewRemoveByShares(uint256 assetId, uint256 shares) external view returns (uint256) {
    return _assets[assetId].toAddedAssetsDown(shares);
  }

  /// @inheritdoc IHubBase
  function previewDrawByAssets(uint256 assetId, uint256 assets) external view returns (uint256) {
    return _assets[assetId].toDrawnSharesUp(assets);
  }

  /// @inheritdoc IHubBase
  function previewDrawByShares(uint256 assetId, uint256 shares) external view returns (uint256) {
    return _assets[assetId].toDrawnAssetsDown(shares);
  }

  /// @inheritdoc IHubBase
  function previewRestoreByAssets(uint256 assetId, uint256 assets) external view returns (uint256) {
    return _assets[assetId].toDrawnSharesDown(assets);
  }

  /// @inheritdoc IHubBase
  function previewRestoreByShares(uint256 assetId, uint256 shares) external view returns (uint256) {
    return _assets[assetId].toDrawnAssetsUp(shares);
  }

  /// @inheritdoc IHubBase
  function getAssetId(address underlying) external view returns (uint256) {
    require(isUnderlyingListed(underlying), AssetNotListed());
    return _underlyingToAssetId[underlying];
  }

  /// @inheritdoc IHubBase
  function getAssetUnderlyingAndDecimals(uint256 assetId) external view returns (address, uint8) {
    Asset storage asset = _assets[assetId];
    return (asset.underlying, asset.decimals);
  }

  /// @inheritdoc IHubBase
  function getAssetDrawnIndex(uint256 assetId) external view returns (uint256) {
    return _assets[assetId].getDrawnIndex();
  }

  /// @inheritdoc IHubBase
  function getAddedAssets(uint256 assetId) external view returns (uint256) {
    return _assets[assetId].totalAddedAssets();
  }

  /// @inheritdoc IHubBase
  function getAddedShares(uint256 assetId) external view returns (uint256) {
    return _assets[assetId].addedShares;
  }

  /// @inheritdoc IHubBase
  function getAssetOwed(uint256 assetId) external view returns (uint256, uint256) {
    Asset storage asset = _assets[assetId];
    uint256 drawnIndex = asset.getDrawnIndex();
    return (asset.drawn(drawnIndex), asset.premium(drawnIndex));
  }

  /// @inheritdoc IHubBase
  function getAssetTotalOwed(uint256 assetId) external view returns (uint256) {
    Asset storage asset = _assets[assetId];
    return asset.totalOwed(asset.getDrawnIndex());
  }

  /// @inheritdoc IHubBase
  function getAssetPremiumRay(uint256 assetId) external view returns (uint256) {
    Asset storage asset = _assets[assetId];
    return
      Premium.calculatePremiumRay({
        premiumShares: asset.premiumShares,
        premiumOffsetRay: asset.premiumOffsetRay,
        drawnIndex: asset.getDrawnIndex()
      });
  }

  /// @inheritdoc IHubBase
  function getAssetDrawnShares(uint256 assetId) external view returns (uint256) {
    return _assets[assetId].drawnShares;
  }

  /// @inheritdoc IHubBase
  function getAssetPremiumData(uint256 assetId) external view returns (uint256, int256) {
    Asset storage asset = _assets[assetId];
    return (asset.premiumShares, asset.premiumOffsetRay);
  }

  /// @inheritdoc IHubBase
  function getAssetLiquidity(uint256 assetId) external view returns (uint256) {
    return _assets[assetId].liquidity;
  }

  /// @inheritdoc IHubBase
  function getAssetDeficitRay(uint256 assetId) external view returns (uint256) {
    return _assets[assetId].deficitRay;
  }

  /// @inheritdoc IHub
  function getAsset(uint256 assetId) external view returns (Asset memory) {
    return _assets[assetId];
  }

  /// @inheritdoc IHub
  function getAssetConfig(uint256 assetId) external view returns (AssetConfig memory) {
    Asset storage asset = _assets[assetId];
    return
      AssetConfig({
        feeReceiver: asset.feeReceiver,
        liquidityFee: asset.liquidityFee,
        irStrategy: asset.irStrategy,
        reinvestmentController: asset.reinvestmentController
      });
  }

  /// @inheritdoc IHub
  function getAssetAccruedFees(uint256 assetId) external view returns (uint256) {
    Asset storage asset = _assets[assetId];
    return asset.realizedFees + asset.getUnrealizedFees(asset.getDrawnIndex());
  }

  /// @inheritdoc IHub
  function getAssetSwept(uint256 assetId) external view returns (uint256) {
    return _assets[assetId].swept;
  }

  /// @inheritdoc IHub
  function getAssetDrawnRate(uint256 assetId) external view returns (uint256) {
    Asset storage asset = _assets[assetId];
    return asset.getDrawnRate(assetId, asset.getDrawnIndex());
  }

  /// @inheritdoc IHub
  function getSpokeCount(uint256 assetId) external view returns (uint256) {
    return _assetToSpokes[assetId].length();
  }

  /// @inheritdoc IHubBase
  function getSpokeAddedAssets(uint256 assetId, address spoke) external view returns (uint256) {
    return _assets[assetId].toAddedAssetsDown(_spokes[assetId][spoke].addedShares);
  }

  /// @inheritdoc IHubBase
  function getSpokeAddedShares(uint256 assetId, address spoke) external view returns (uint256) {
    return _spokes[assetId][spoke].addedShares;
  }

  /// @inheritdoc IHubBase
  function getSpokeOwed(uint256 assetId, address spoke) external view returns (uint256, uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spokeData = _spokes[assetId][spoke];
    return (_getSpokeDrawn(asset, spokeData), _getSpokePremium(asset, spokeData));
  }

  /// @inheritdoc IHubBase
  function getSpokeTotalOwed(uint256 assetId, address spoke) external view returns (uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spokeData = _spokes[assetId][spoke];
    return _getSpokeDrawn(asset, spokeData) + _getSpokePremium(asset, spokeData);
  }

  /// @inheritdoc IHubBase
  function getSpokePremiumRay(uint256 assetId, address spoke) external view returns (uint256) {
    Asset storage asset = _assets[assetId];
    SpokeData storage spokeData = _spokes[assetId][spoke];
    return _getSpokePremiumRay(asset, spokeData);
  }

  /// @inheritdoc IHubBase
  function getSpokeDrawnShares(uint256 assetId, address spoke) external view returns (uint256) {
    return _spokes[assetId][spoke].drawnShares;
  }

  /// @inheritdoc IHubBase
  function getSpokePremiumData(
    uint256 assetId,
    address spoke
  ) external view returns (uint256, int256) {
    SpokeData storage spokeData = _spokes[assetId][spoke];
    return (spokeData.premiumShares, spokeData.premiumOffsetRay);
  }

  /// @inheritdoc IHubBase
  function getSpokeDeficitRay(uint256 assetId, address spoke) external view returns (uint256) {
    return _spokes[assetId][spoke].deficitRay;
  }

  /// @inheritdoc IHub
  function isSpokeListed(uint256 assetId, address spoke) external view returns (bool) {
    return _assetToSpokes[assetId].contains(spoke);
  }

  /// @inheritdoc IHub
  function getSpokeAddress(uint256 assetId, uint256 index) external view returns (address) {
    return _assetToSpokes[assetId].at(index);
  }

  /// @inheritdoc IHub
  function getSpoke(uint256 assetId, address spoke) external view returns (SpokeData memory) {
    return _spokes[assetId][spoke];
  }

  /// @inheritdoc IHub
  function getSpokeConfig(
    uint256 assetId,
    address spoke
  ) external view returns (SpokeConfig memory) {
    SpokeData storage spokeData = _spokes[assetId][spoke];
    return
      SpokeConfig({
        addCap: spokeData.addCap,
        drawCap: spokeData.drawCap,
        riskPremiumThreshold: spokeData.riskPremiumThreshold,
        active: spokeData.active,
        halted: spokeData.halted
      });
  }

  /// @notice Adds a new spoke to an asset with default feeReceiver configuration (maximum add cap, zero draw cap).
  function _addFeeReceiver(uint256 assetId, address feeReceiver) internal {
    _addSpoke(assetId, feeReceiver);
    _updateSpokeConfig(
      assetId,
      feeReceiver,
      SpokeConfig({
        addCap: MAX_ALLOWED_SPOKE_CAP,
        drawCap: 0,
        riskPremiumThreshold: 0,
        active: true,
        halted: false
      })
    );
  }

  /// @notice Adds a spoke to an asset.
  /// @dev Reverts with `SpokeAlreadyListed` if spoke is already listed for the given asset.
  function _addSpoke(uint256 assetId, address spoke) internal {
    require(_assetToSpokes[assetId].add(spoke), SpokeAlreadyListed());
    emit AddSpoke(assetId, spoke);
  }

  function _updateSpokeConfig(uint256 assetId, address spoke, SpokeConfig memory config) internal {
    SpokeData storage spokeData = _spokes[assetId][spoke];
    spokeData.addCap = config.addCap;
    spokeData.drawCap = config.drawCap;
    spokeData.riskPremiumThreshold = config.riskPremiumThreshold;
    spokeData.active = config.active;
    spokeData.halted = config.halted;
    emit UpdateSpokeConfig(assetId, spoke, config);
  }

  /// @dev Receiver `addCap` is validated in `_validateTransferShares`.
  function _transferShares(
    SpokeData storage sender,
    SpokeData storage receiver,
    uint256 shares
  ) internal {
    sender.addedShares -= shares.toUint120();
    receiver.addedShares += shares.toUint120();
  }

  /// @dev Applies premium deltas on asset & spoke premium owed.
  /// @dev Checks premium owed decreases by exactly `restoredPremiumRay`.
  /// @dev Checks updated risk premium is within allowed threshold.
  /// @dev Uses last stored index; asset accrual should have already occurred.
  function _applyPremiumDelta(
    Asset storage asset,
    SpokeData storage spoke,
    PremiumDelta calldata premiumDelta
  ) internal {
    uint256 drawnIndex = asset.drawnIndex;

    // asset premium change
    (asset.premiumShares, asset.premiumOffsetRay) = _validateApplyPremiumDelta(
      drawnIndex,
      asset.premiumShares,
      asset.premiumOffsetRay,
      premiumDelta
    );

    // spoke premium change
    (spoke.premiumShares, spoke.premiumOffsetRay) = _validateApplyPremiumDelta(
      drawnIndex,
      spoke.premiumShares,
      spoke.premiumOffsetRay,
      premiumDelta
    );

    uint24 riskPremiumThreshold = spoke.riskPremiumThreshold;
    require(
      riskPremiumThreshold == MAX_RISK_PREMIUM_THRESHOLD ||
        spoke.premiumShares <= spoke.drawnShares.percentMulUp(riskPremiumThreshold),
      InvalidPremiumChange()
    );
  }

  function _mintFeeShares(Asset storage asset, uint256 assetId) internal returns (uint256) {
    uint256 fees = asset.realizedFees;
    uint120 shares = asset.toAddedSharesDown(fees).toUint120();
    if (shares == 0) {
      return 0;
    }

    address feeReceiver = asset.feeReceiver;
    SpokeData storage feeReceiverSpoke = _spokes[assetId][feeReceiver];
    require(feeReceiverSpoke.active, SpokeNotActive());

    asset.addedShares += shares;
    feeReceiverSpoke.addedShares += shares;
    asset.realizedFees = 0;
    emit MintFeeShares(assetId, feeReceiver, shares, fees);

    return shares;
  }

  /// @dev Returns the Spoke's drawn amount for a specified asset.
  function _getSpokeDrawn(
    Asset storage asset,
    SpokeData storage spoke
  ) internal view returns (uint256) {
    return asset.toDrawnAssetsUp(spoke.drawnShares);
  }

  /// @dev Returns the Spoke's premium amount for a specified asset.
  function _getSpokePremium(
    Asset storage asset,
    SpokeData storage spoke
  ) internal view returns (uint256) {
    return _getSpokePremiumRay(asset, spoke).fromRayUp();
  }

  /// @dev Returns the Spoke's premium amount with full precision for a specified asset.
  function _getSpokePremiumRay(
    Asset storage asset,
    SpokeData storage spoke
  ) internal view returns (uint256) {
    return
      Premium.calculatePremiumRay({
        premiumShares: spoke.premiumShares,
        premiumOffsetRay: spoke.premiumOffsetRay,
        drawnIndex: asset.getDrawnIndex()
      });
  }

  /// @dev Spoke with maximum cap have unlimited add capacity.
  function _validateAdd(
    Asset storage asset,
    SpokeData storage spoke,
    uint256 amount
  ) internal view {
    require(amount > 0, InvalidAmount());
    require(spoke.active, SpokeNotActive());
    require(!spoke.halted, SpokeHalted());
    uint256 addCap = spoke.addCap;
    require(
      addCap == MAX_ALLOWED_SPOKE_CAP ||
        addCap * MathUtils.uncheckedExp(10, asset.decimals) >=
          asset.toAddedAssetsUp(spoke.addedShares) + amount,
      AddCapExceeded(addCap)
    );
  }

  function _validateRemove(SpokeData storage spoke, uint256 amount, address to) internal view {
    require(to != address(this), InvalidAddress());
    require(amount > 0, InvalidAmount());
    require(spoke.active, SpokeNotActive());
    require(!spoke.halted, SpokeHalted());
  }

  /// @dev The draw cap is enforced against the Spoke's total owed, including any reported deficit.
  /// @dev Spoke with maximum cap have unlimited draw capacity.
  function _validateDraw(
    Asset storage asset,
    SpokeData storage spoke,
    uint256 amount,
    address to
  ) internal view {
    require(to != address(this), InvalidAddress());
    require(amount > 0, InvalidAmount());
    require(spoke.active, SpokeNotActive());
    require(!spoke.halted, SpokeHalted());
    uint256 drawCap = spoke.drawCap;
    uint256 owed = _getSpokeDrawn(asset, spoke) + _getSpokePremium(asset, spoke);
    require(
      drawCap == MAX_ALLOWED_SPOKE_CAP ||
        drawCap * MathUtils.uncheckedExp(10, asset.decimals) >=
          owed + amount + uint256(spoke.deficitRay).fromRayUp(),
      DrawCapExceeded(drawCap)
    );
  }

  function _validateRestore(
    Asset storage asset,
    SpokeData storage spoke,
    uint256 drawnAmount,
    uint256 premiumAmountRay
  ) internal view {
    require(drawnAmount > 0 || premiumAmountRay > 0, InvalidAmount());
    require(spoke.active, SpokeNotActive());
    require(!spoke.halted, SpokeHalted());
    uint256 drawn = _getSpokeDrawn(asset, spoke);
    uint256 premiumRay = _getSpokePremiumRay(asset, spoke);
    require(drawnAmount <= drawn, SurplusDrawnRestored(drawn));
    require(premiumAmountRay <= premiumRay, SurplusPremiumRayRestored(premiumRay));
  }

  function _validateReportDeficit(
    Asset storage asset,
    SpokeData storage spoke,
    uint256 drawnAmount,
    uint256 premiumAmountRay
  ) internal view {
    require(drawnAmount > 0 || premiumAmountRay > 0, InvalidAmount());
    require(spoke.active, SpokeNotActive());
    uint256 drawn = _getSpokeDrawn(asset, spoke);
    uint256 premiumRay = _getSpokePremiumRay(asset, spoke);
    require(drawnAmount <= drawn, SurplusDrawnDeficitReported(drawn));
    require(premiumAmountRay <= premiumRay, SurplusPremiumRayDeficitReported(premiumRay));
  }

  function _validateEliminateDeficit(
    SpokeData storage callerSpoke,
    uint256 deficitAmountRay
  ) internal view {
    require(callerSpoke.active, SpokeNotActive());
    require(deficitAmountRay > 0, InvalidAmount());
  }

  function _validatePayFeeShares(SpokeData storage callerSpoke, uint256 feeShares) internal view {
    require(callerSpoke.active, SpokeNotActive());
    require(feeShares > 0, InvalidShares());
  }

  function _validateTransferShares(
    Asset storage asset,
    SpokeData storage callerSpoke,
    SpokeData storage receiverSpoke,
    uint256 shares
  ) internal view {
    require(callerSpoke.active && receiverSpoke.active, SpokeNotActive());
    require(!callerSpoke.halted && !receiverSpoke.halted, SpokeHalted());
    require(shares > 0, InvalidShares());
    uint256 addCap = receiverSpoke.addCap;
    require(
      addCap == MAX_ALLOWED_SPOKE_CAP ||
        addCap * MathUtils.uncheckedExp(10, asset.decimals) >=
          asset.toAddedAssetsUp(receiverSpoke.addedShares + shares),
      AddCapExceeded(addCap)
    );
  }

  function _validateSweep(Asset storage asset, address caller, uint256 amount) internal view {
    // sufficient check to disallow when controller unset
    require(caller == asset.reinvestmentController, OnlyReinvestmentController());
    require(amount > 0, InvalidAmount());
  }

  function _validateReclaim(Asset storage asset, address caller, uint256 amount) internal view {
    // sufficient check to disallow when controller unset
    require(caller == asset.reinvestmentController, OnlyReinvestmentController());
    require(amount > 0, InvalidAmount());
  }

  /// @dev Validates applied premium delta for given premium data and returns updated premium data.
  function _validateApplyPremiumDelta(
    uint256 drawnIndex,
    uint256 premiumShares,
    int256 premiumOffsetRay,
    PremiumDelta calldata premiumDelta
  ) internal pure returns (uint120, int200) {
    uint256 premiumRayBefore = Premium.calculatePremiumRay({
      premiumShares: premiumShares,
      premiumOffsetRay: premiumOffsetRay,
      drawnIndex: drawnIndex
    });

    uint256 newPremiumShares = premiumShares.add(premiumDelta.sharesDelta);
    int256 newPremiumOffsetRay = premiumOffsetRay + premiumDelta.offsetRayDelta;

    uint256 premiumRayAfter = Premium.calculatePremiumRay({
      premiumShares: newPremiumShares,
      premiumOffsetRay: newPremiumOffsetRay,
      drawnIndex: drawnIndex
    });

    require(
      premiumRayAfter + premiumDelta.restoredPremiumRay == premiumRayBefore,
      InvalidPremiumChange()
    );
    return (newPremiumShares.toUint120(), newPremiumOffsetRay.toInt200());
  }
}

// bench/HubOperations.sol

contract AlwaysAllowAuthority {
  function canCall(address, address, bytes4) external pure returns (bool, uint32) {
    return (true, 0);
  }
}

contract TestHub is Hub {
  constructor(address authority_) initializer {
    __AccessManaged_init(authority_);
  }

  function initialize(address) external pure override {}
}

contract HubActor {
  TestHub public immutable hub;
  TestnetERC20 public immutable token;
  uint256 public immutable assetId;

  constructor(TestHub hub_, TestnetERC20 token_, uint256 assetId_) {
    hub = hub_;
    token = token_;
    assetId = assetId_;
  }

  function transferToHub(uint256 amount) external {
    token.transfer(address(hub), amount);
  }

  function add(uint256 amount) external {
    hub.add(assetId, amount);
  }

  function addWithTransfer(uint256 amount) external {
    token.transfer(address(hub), amount);
    hub.add(assetId, amount);
  }

  function remove(uint256 amount) external {
    hub.remove(assetId, amount, address(this));
  }

  function draw(uint256 amount) external {
    hub.draw(assetId, amount, address(this));
  }

  function restore(uint256 amount) external {
    token.transfer(address(hub), amount);
    hub.restore(assetId, amount, IHubBase.PremiumDelta(0, 0, 0));
  }

  function reportDeficit(uint256 amount) external {
    hub.reportDeficit(assetId, amount, IHubBase.PremiumDelta(0, 0, 0));
  }

  function eliminateDeficit(uint256 amount, address coveredSpoke) external {
    hub.eliminateDeficit(assetId, amount, coveredSpoke);
  }
}

contract AGasTest {
  TestHub public immutable hub;
  TestnetERC20 public immutable dai;
  uint256 public immutable assetId;

  HubActor private immutable addActor;
  HubActor private immutable removeActor;
  HubActor private immutable drawActor;
  HubActor private immutable restoreActor;
  HubActor private immutable deficitActor;

  constructor() {
    AlwaysAllowAuthority authority = new AlwaysAllowAuthority();
    hub = new TestHub(address(authority));
    AssetInterestRateStrategy strategy = new AssetInterestRateStrategy(address(hub));
    dai = new TestnetERC20('DAI', 'DAI', 18);
    IAssetInterestRateStrategy.InterestRateData memory rateData =
      IAssetInterestRateStrategy.InterestRateData({
        optimalUsageRatio: 90_00,
        baseDrawnRate: 5_00,
        rateGrowthBeforeOptimal: 5_00,
        rateGrowthAfterOptimal: 5_00
      });
    assetId = hub.addAsset(
      address(dai), 18, address(this), address(strategy), abi.encode(rateData)
    );

    addActor = _newActor();
    removeActor = _newActor();
    drawActor = _newActor();
    restoreActor = _newActor();
    deficitActor = _newActor();

    // Prepare independent positions so each measured method follows the same
    // state shape and values as its upstream Hub.Operations gas scenario.
    addActor.transferToHub(1000e6);

    removeActor.addWithTransfer(1000e6);

    drawActor.addWithTransfer(1000e18);

    restoreActor.addWithTransfer(1000e18);
    restoreActor.draw(500e18);

    deficitActor.addWithTransfer(1000e18);
    deficitActor.draw(500e18);
  }

  function _newActor() internal returns (HubActor actor) {
    actor = new HubActor(hub, dai, assetId);
    dai.mint(address(actor), 3000e18);
    hub.addSpoke(assetId, address(actor), IHub.SpokeConfig({
      addCap: type(uint40).max,
      drawCap: type(uint40).max,
      riskPremiumThreshold: type(uint24).max,
      active: true,
      halted: false
    }));
  }

  function add() external {
    addActor.add(1000e6);
  }

  function addWithTransfer() external {
    addActor.addWithTransfer(1000e6);
  }

  function removePartial() external {
    removeActor.remove(500e6);
  }

  function removeFull() external {
    removeActor.remove(500e6);
  }

  function draw() external {
    drawActor.draw(500e18);
  }

  function restorePartial() external {
    restoreActor.restore(250e18);
  }

  function restoreFull() external {
    restoreActor.restore(250e18);
  }

  function reportDeficit() external {
    deficitActor.reportDeficit(500e18);
  }

  function eliminateDeficitPartial() external {
    deficitActor.eliminateDeficit(100e18, address(deficitActor));
  }

  function eliminateDeficitFull() external {
    deficitActor.eliminateDeficit(type(uint256).max, address(deficitActor));
  }
}

// ----
// add() -> 0
// addWithTransfer() -> 0
// removePartial() -> 0
// removeFull() -> 0
// draw() -> 0
// restorePartial() -> 0
// restoreFull() -> 0
// reportDeficit() -> 0
// eliminateDeficitPartial() -> 0
// eliminateDeficitFull() -> 0
