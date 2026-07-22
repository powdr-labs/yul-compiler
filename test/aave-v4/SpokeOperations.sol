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

// src/dependencies/openzeppelin/ECDSA.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/cryptography/ECDSA.sol)

/**
 * @dev Elliptic Curve Digital Signature Algorithm (ECDSA) operations.
 *
 * These functions can be used to verify that a message was signed by the holder
 * of the private keys of a given address.
 */
library ECDSA {
  enum RecoverError {
    NoError,
    InvalidSignature,
    InvalidSignatureLength,
    InvalidSignatureS
  }

  /**
   * @dev The signature derives the `address(0)`.
   */
  error ECDSAInvalidSignature();

  /**
   * @dev The signature has an invalid length.
   */
  error ECDSAInvalidSignatureLength(uint256 length);

  /**
   * @dev The signature has an S value that is in the upper half order.
   */
  error ECDSAInvalidSignatureS(bytes32 s);

  /**
   * @dev Returns the address that signed a hashed message (`hash`) with `signature` or an error. This will not
   * return address(0) without also returning an error description. Errors are documented using an enum (error type)
   * and a bytes32 providing additional information about the error.
   *
   * If no error is returned, then the address can be used for verification purposes.
   *
   * The `ecrecover` EVM precompile allows for malleable (non-unique) signatures:
   * this function rejects them by requiring the `s` value to be in the lower
   * half order, and the `v` value to be either 27 or 28.
   *
   * NOTE: This function only supports 65-byte signatures. ERC-2098 short signatures are rejected. This restriction
   * is DEPRECATED and will be removed in v6.0. Developers SHOULD NOT use signatures as unique identifiers; use hash
   * invalidation or nonces for replay protection.
   *
   * IMPORTANT: `hash` _must_ be the result of a hash operation for the
   * verification to be secure: it is possible to craft signatures that
   * recover to arbitrary addresses for non-hashed data. A safe way to ensure
   * this is by receiving a hash of the original message (which may otherwise
   * be too long), and then calling {MessageHashUtils-toEthSignedMessageHash} on it.
   *
   * Documentation for signature generation:
   *
   * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
   * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
   */
  function tryRecover(
    bytes32 hash,
    bytes memory signature
  ) internal pure returns (address recovered, RecoverError err, bytes32 errArg) {
    if (signature.length == 65) {
      bytes32 r;
      bytes32 s;
      uint8 v;
      // ecrecover takes the signature parameters, and the only way to get them
      // currently is to use assembly.
      assembly ('memory-safe') {
        r := mload(add(signature, 0x20))
        s := mload(add(signature, 0x40))
        v := byte(0, mload(add(signature, 0x60)))
      }
      return tryRecover(hash, v, r, s);
    } else {
      return (address(0), RecoverError.InvalidSignatureLength, bytes32(signature.length));
    }
  }

  /**
   * @dev Variant of {tryRecover} that takes a signature in calldata
   */
  function tryRecoverCalldata(
    bytes32 hash,
    bytes calldata signature
  ) internal pure returns (address recovered, RecoverError err, bytes32 errArg) {
    if (signature.length == 65) {
      bytes32 r;
      bytes32 s;
      uint8 v;
      // ecrecover takes the signature parameters, calldata slices would work here, but are
      // significantly more expensive (length check) than using calldataload in assembly.
      assembly ('memory-safe') {
        r := calldataload(signature.offset)
        s := calldataload(add(signature.offset, 0x20))
        v := byte(0, calldataload(add(signature.offset, 0x40)))
      }
      return tryRecover(hash, v, r, s);
    } else {
      return (address(0), RecoverError.InvalidSignatureLength, bytes32(signature.length));
    }
  }

  /**
   * @dev Returns the address that signed a hashed message (`hash`) with
   * `signature`. This address can then be used for verification purposes.
   *
   * The `ecrecover` EVM precompile allows for malleable (non-unique) signatures:
   * this function rejects them by requiring the `s` value to be in the lower
   * half order, and the `v` value to be either 27 or 28.
   *
   * NOTE: This function only supports 65-byte signatures. ERC-2098 short signatures are rejected. This restriction
   * is DEPRECATED and will be removed in v6.0. Developers SHOULD NOT use signatures as unique identifiers; use hash
   * invalidation or nonces for replay protection.
   *
   * IMPORTANT: `hash` _must_ be the result of a hash operation for the
   * verification to be secure: it is possible to craft signatures that
   * recover to arbitrary addresses for non-hashed data. A safe way to ensure
   * this is by receiving a hash of the original message (which may otherwise
   * be too long), and then calling {MessageHashUtils-toEthSignedMessageHash} on it.
   */
  function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
    (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, signature);
    _throwError(error, errorArg);
    return recovered;
  }

  /**
   * @dev Variant of {recover} that takes a signature in calldata
   */
  function recoverCalldata(bytes32 hash, bytes calldata signature) internal pure returns (address) {
    (address recovered, RecoverError error, bytes32 errorArg) = tryRecoverCalldata(hash, signature);
    _throwError(error, errorArg);
    return recovered;
  }

  /**
   * @dev Overload of {ECDSA-tryRecover} that receives the `r` and `vs` short-signature fields separately.
   *
   * See https://eips.ethereum.org/EIPS/eip-2098[ERC-2098 short signatures]
   */
  function tryRecover(
    bytes32 hash,
    bytes32 r,
    bytes32 vs
  ) internal pure returns (address recovered, RecoverError err, bytes32 errArg) {
    unchecked {
      bytes32 s = vs & bytes32(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      // We do not check for an overflow here since the shift operation results in 0 or 1.
      uint8 v = uint8((uint256(vs) >> 255) + 27);
      return tryRecover(hash, v, r, s);
    }
  }

  /**
   * @dev Overload of {ECDSA-recover} that receives the `r and `vs` short-signature fields separately.
   */
  function recover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address) {
    (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, r, vs);
    _throwError(error, errorArg);
    return recovered;
  }

  /**
   * @dev Overload of {ECDSA-tryRecover} that receives the `v`,
   * `r` and `s` signature fields separately.
   */
  function tryRecover(
    bytes32 hash,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) internal pure returns (address recovered, RecoverError err, bytes32 errArg) {
    // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
    // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
    // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
    // signatures from current libraries generate a unique signature with an s-value in the lower half order.
    //
    // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
    // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
    // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
    // these malleable signatures as well.
    if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
      return (address(0), RecoverError.InvalidSignatureS, s);
    }

    // If the signature is valid (and not malleable), return the signer address
    address signer = ecrecover(hash, v, r, s);
    if (signer == address(0)) {
      return (address(0), RecoverError.InvalidSignature, bytes32(0));
    }

    return (signer, RecoverError.NoError, bytes32(0));
  }

  /**
   * @dev Overload of {ECDSA-recover} that receives the `v`,
   * `r` and `s` signature fields separately.
   */
  function recover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal pure returns (address) {
    (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, v, r, s);
    _throwError(error, errorArg);
    return recovered;
  }

  /**
   * @dev Parse a signature into its `v`, `r` and `s` components. Supports 65-byte and 64-byte (ERC-2098)
   * formats. Returns (0,0,0) for invalid signatures.
   *
   * For 64-byte signatures, `v` is automatically normalized to 27 or 28.
   * For 65-byte signatures, `v` is returned as-is and MUST already be 27 or 28 for use with ecrecover.
   *
   * Consider validating the result before use, or use {tryRecover}/{recover} which perform full validation.
   */
  function parse(bytes memory signature) internal pure returns (uint8 v, bytes32 r, bytes32 s) {
    assembly ('memory-safe') {
      // Check the signature length
      switch mload(signature)
      // - case 65: r,s,v signature (standard)
      case 65 {
        r := mload(add(signature, 0x20))
        s := mload(add(signature, 0x40))
        v := byte(0, mload(add(signature, 0x60)))
      }
      // - case 64: r,vs signature (cf https://eips.ethereum.org/EIPS/eip-2098)
      case 64 {
        let vs := mload(add(signature, 0x40))
        r := mload(add(signature, 0x20))
        s := and(vs, shr(1, not(0)))
        v := add(shr(255, vs), 27)
      }
      default {
        r := 0
        s := 0
        v := 0
      }
    }
  }

  /**
   * @dev Variant of {parse} that takes a signature in calldata
   */
  function parseCalldata(
    bytes calldata signature
  ) internal pure returns (uint8 v, bytes32 r, bytes32 s) {
    assembly ('memory-safe') {
      // Check the signature length
      switch signature.length
      // - case 65: r,s,v signature (standard)
      case 65 {
        r := calldataload(signature.offset)
        s := calldataload(add(signature.offset, 0x20))
        v := byte(0, calldataload(add(signature.offset, 0x40)))
      }
      // - case 64: r,vs signature (cf https://eips.ethereum.org/EIPS/eip-2098)
      case 64 {
        let vs := calldataload(add(signature.offset, 0x20))
        r := calldataload(signature.offset)
        s := and(vs, shr(1, not(0)))
        v := add(shr(255, vs), 27)
      }
      default {
        r := 0
        s := 0
        v := 0
      }
    }
  }

  /**
   * @dev Optionally reverts with the corresponding custom error according to the `error` argument provided.
   */
  function _throwError(RecoverError error, bytes32 errorArg) private pure {
    if (error == RecoverError.NoError) {
      return; // no error: do nothing
    } else if (error == RecoverError.InvalidSignature) {
      revert ECDSAInvalidSignature();
    } else if (error == RecoverError.InvalidSignatureLength) {
      revert ECDSAInvalidSignatureLength(uint256(errorArg));
    } else if (error == RecoverError.InvalidSignatureS) {
      revert ECDSAInvalidSignatureS(errorArg);
    }
  }
}

// src/dependencies/solady/EIP712.sol

/// @notice Contract for EIP-712 typed structured data hashing and signing.
/// @author Solady (https://github.com/vectorized/solady/blob/main/src/utils/EIP712.sol)
/// @author Modified from Solbase (https://github.com/Sol-DAO/solbase/blob/main/src/utils/EIP712.sol)
/// @author Modified from OpenZeppelin (https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/utils/cryptography/EIP712.sol)
///
/// @dev Note, this implementation:
/// - Uses `address(this)` for the `verifyingContract` field.
/// - Does NOT use the optional EIP-712 salt.
/// - Does NOT use any EIP-712 extensions.
/// This is for simplicity and to save gas.
/// If you need to customize, please fork / modify accordingly.
abstract contract EIP712 {
  /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
  /*                  CONSTANTS AND IMMUTABLES                  */
  /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

  /// @dev `keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")`.
  bytes32 internal constant _DOMAIN_TYPEHASH =
    0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f;

  uint256 private immutable _cachedThis;
  uint256 private immutable _cachedChainId;
  bytes32 private immutable _cachedNameHash;
  bytes32 private immutable _cachedVersionHash;
  bytes32 private immutable _cachedDomainSeparator;

  /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
  /*                        CONSTRUCTOR                         */
  /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

  /// @dev Cache the hashes for cheaper runtime gas costs.
  /// In the case of upgradeable contracts (i.e. proxies),
  /// or if the chain id changes due to a hard fork,
  /// the domain separator will be seamlessly calculated on-the-fly.
  constructor() {
    _cachedThis = uint256(uint160(address(this)));
    _cachedChainId = block.chainid;

    string memory name;
    string memory version;
    if (!_domainNameAndVersionMayChange()) (name, version) = _domainNameAndVersion();
    bytes32 nameHash = _domainNameAndVersionMayChange() ? bytes32(0) : keccak256(bytes(name));
    bytes32 versionHash = _domainNameAndVersionMayChange() ? bytes32(0) : keccak256(bytes(version));
    _cachedNameHash = nameHash;
    _cachedVersionHash = versionHash;

    bytes32 separator;
    if (!_domainNameAndVersionMayChange()) {
      /// @solidity memory-safe-assembly
      assembly {
        let m := mload(0x40) // Load the free memory pointer.
        mstore(m, _DOMAIN_TYPEHASH)
        mstore(add(m, 0x20), nameHash)
        mstore(add(m, 0x40), versionHash)
        mstore(add(m, 0x60), chainid())
        mstore(add(m, 0x80), address())
        separator := keccak256(m, 0xa0)
      }
    }
    _cachedDomainSeparator = separator;
  }

  /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
  /*                   FUNCTIONS TO OVERRIDE                    */
  /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

  /// @dev Please override this function to return the domain name and version.
  /// ```
  ///     function _domainNameAndVersion()
  ///         internal
  ///         pure
  ///         virtual
  ///         returns (string memory name, string memory version)
  ///     {
  ///         name = "Solady";
  ///         version = "1";
  ///     }
  /// ```
  ///
  /// Note: If the returned result may change after the contract has been deployed,
  /// you must override `_domainNameAndVersionMayChange()` to return true.
  function _domainNameAndVersion()
    internal
    view
    virtual
    returns (string memory name, string memory version);

  /// @dev Returns if `_domainNameAndVersion()` may change
  /// after the contract has been deployed (i.e. after the constructor).
  /// Default: false.
  function _domainNameAndVersionMayChange() internal pure virtual returns (bool result) {}

  /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
  /*                     HASHING OPERATIONS                     */
  /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

  /// @dev Returns the EIP-712 domain separator.
  function _domainSeparator() internal view virtual returns (bytes32 separator) {
    if (_domainNameAndVersionMayChange()) {
      separator = _buildDomainSeparator();
    } else {
      separator = _cachedDomainSeparator;
      if (_cachedDomainSeparatorInvalidated()) separator = _buildDomainSeparator();
    }
  }

  /// @dev Returns the hash of the fully encoded EIP-712 message for this domain,
  /// given `structHash`, as defined in
  /// https://eips.ethereum.org/EIPS/eip-712#definition-of-hashstruct.
  ///
  /// The hash can be used together with {ECDSA-recover} to obtain the signer of a message:
  /// ```
  ///     bytes32 digest = _hashTypedData(keccak256(abi.encode(
  ///         keccak256("Mail(address to,string contents)"),
  ///         mailTo,
  ///         keccak256(bytes(mailContents))
  ///     )));
  ///     address signer = ECDSA.recover(digest, signature);
  /// ```
  function _hashTypedData(bytes32 structHash) internal view virtual returns (bytes32 digest) {
    // We will use `digest` to store the domain separator to save a bit of gas.
    if (_domainNameAndVersionMayChange()) {
      digest = _buildDomainSeparator();
    } else {
      digest = _cachedDomainSeparator;
      if (_cachedDomainSeparatorInvalidated()) digest = _buildDomainSeparator();
    }
    /// @solidity memory-safe-assembly
    assembly {
      // Compute the digest.
      mstore(0x00, 0x1901000000000000) // Store "\x19\x01".
      mstore(0x1a, digest) // Store the domain separator.
      mstore(0x3a, structHash) // Store the struct hash.
      digest := keccak256(0x18, 0x42)
      // Restore the part of the free memory slot that was overwritten.
      mstore(0x3a, 0)
    }
  }

  /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
  /*                    EIP-5267 OPERATIONS                     */
  /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

  /// @dev See: https://eips.ethereum.org/EIPS/eip-5267
  function eip712Domain()
    public
    view
    virtual
    returns (
      bytes1 fields,
      string memory name,
      string memory version,
      uint256 chainId,
      address verifyingContract,
      bytes32 salt,
      uint256[] memory extensions
    )
  {
    fields = hex'0f'; // `0b01111`.
    (name, version) = _domainNameAndVersion();
    chainId = block.chainid;
    verifyingContract = address(this);
    salt = salt; // `bytes32(0)`.
    extensions = extensions; // `new uint256[](0)`.
  }

  /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
  /*                      PRIVATE HELPERS                       */
  /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

  /// @dev Returns the EIP-712 domain separator.
  function _buildDomainSeparator() private view returns (bytes32 separator) {
    // We will use `separator` to store the name hash to save a bit of gas.
    bytes32 versionHash;
    if (_domainNameAndVersionMayChange()) {
      (string memory name, string memory version) = _domainNameAndVersion();
      separator = keccak256(bytes(name));
      versionHash = keccak256(bytes(version));
    } else {
      separator = _cachedNameHash;
      versionHash = _cachedVersionHash;
    }
    /// @solidity memory-safe-assembly
    assembly {
      let m := mload(0x40) // Load the free memory pointer.
      mstore(m, _DOMAIN_TYPEHASH)
      mstore(add(m, 0x20), separator) // Name hash.
      mstore(add(m, 0x40), versionHash)
      mstore(add(m, 0x60), chainid())
      mstore(add(m, 0x80), address())
      separator := keccak256(m, 0xa0)
    }
  }

  /// @dev Returns if the cached domain separator has been invalidated.
  function _cachedDomainSeparatorInvalidated() private view returns (bool result) {
    uint256 cachedChainId = _cachedChainId;
    uint256 cachedThis = _cachedThis;
    /// @solidity memory-safe-assembly
    assembly {
      result := iszero(and(eq(chainid(), cachedChainId), eq(address(), cachedThis)))
    }
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

// src/dependencies/openzeppelin/IERC1271.sol

// OpenZeppelin Contracts (last updated v5.4.0) (interfaces/IERC1271.sol)

/**
 * @dev Interface of the ERC-1271 standard signature validation method for
 * contracts as defined in https://eips.ethereum.org/EIPS/eip-1271[ERC-1271].
 */
interface IERC1271 {
  /**
   * @dev Should return whether the signature provided is valid for the provided data
   * @param hash      Hash of the data to be signed
   * @param signature Signature byte array associated with `hash`
   */
  function isValidSignature(
    bytes32 hash,
    bytes calldata signature
  ) external view returns (bytes4 magicValue);
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

// src/dependencies/openzeppelin/IERC7913.sol

// OpenZeppelin Contracts (last updated v5.4.0) (interfaces/IERC7913.sol)

/**
 * @dev Signature verifier interface.
 */
interface IERC7913SignatureVerifier {
  /**
   * @dev Verifies `signature` as a valid signature of `hash` by `key`.
   *
   * MUST return the bytes4 magic value IERC7913SignatureVerifier.verify.selector if the signature is valid.
   * SHOULD return 0xffffffff or revert if the signature is not valid.
   * SHOULD return 0xffffffff or revert if the key is empty
   */
  function verify(
    bytes calldata key,
    bytes32 hash,
    bytes calldata signature
  ) external view returns (bytes4);
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

// src/spoke/interfaces/IPriceFeed.sol

/// @title IPriceFeed
/// @author Aave Labs
/// @notice Defines the minimal functions needed to work with the AaveOracle contract.
interface IPriceFeed {
  /// @notice Returns the number of decimals used to represent the price.
  function decimals() external view returns (uint8);

  /// @notice Returns the description of the feed.
  function description() external view returns (string memory);

  /// @notice Returns the latest price answer, expressed with `decimals` precision.
  function latestAnswer() external view returns (int256);
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

// src/dependencies/openzeppelin/TransientSlot.sol

// OpenZeppelin Contracts (last updated v5.3.0) (utils/TransientSlot.sol)
// This file was procedurally generated from scripts/generate/templates/TransientSlot.js.

/**
 * @dev Library for reading and writing value-types to specific transient storage slots.
 *
 * Transient slots are often used to store temporary values that are removed after the current transaction.
 * This library helps with reading and writing to such slots without the need for inline assembly.
 *
 *  * Example reading and writing values using transient storage:
 * ```solidity
 * contract Lock {
 *     using TransientSlot for *;
 *
 *     // Define the slot. Alternatively, use the SlotDerivation library to derive the slot.
 *     bytes32 internal constant _LOCK_SLOT = 0xf4678858b2b588224636b8522b729e7722d32fc491da849ed75b3fdf3c84f542;
 *
 *     modifier locked() {
 *         require(!_LOCK_SLOT.asBoolean().tload());
 *
 *         _LOCK_SLOT.asBoolean().tstore(true);
 *         _;
 *         _LOCK_SLOT.asBoolean().tstore(false);
 *     }
 * }
 * ```
 *
 * TIP: Consider using this library along with {SlotDerivation}.
 */
library TransientSlot {
  /**
   * @dev UDVT that represents a slot holding an address.
   */
  type AddressSlot is bytes32;

  /**
   * @dev Cast an arbitrary slot to a AddressSlot.
   */
  function asAddress(bytes32 slot) internal pure returns (AddressSlot) {
    return AddressSlot.wrap(slot);
  }

  /**
   * @dev UDVT that represents a slot holding a bool.
   */
  type BooleanSlot is bytes32;

  /**
   * @dev Cast an arbitrary slot to a BooleanSlot.
   */
  function asBoolean(bytes32 slot) internal pure returns (BooleanSlot) {
    return BooleanSlot.wrap(slot);
  }

  /**
   * @dev UDVT that represents a slot holding a bytes32.
   */
  type Bytes32Slot is bytes32;

  /**
   * @dev Cast an arbitrary slot to a Bytes32Slot.
   */
  function asBytes32(bytes32 slot) internal pure returns (Bytes32Slot) {
    return Bytes32Slot.wrap(slot);
  }

  /**
   * @dev UDVT that represents a slot holding a uint256.
   */
  type Uint256Slot is bytes32;

  /**
   * @dev Cast an arbitrary slot to a Uint256Slot.
   */
  function asUint256(bytes32 slot) internal pure returns (Uint256Slot) {
    return Uint256Slot.wrap(slot);
  }

  /**
   * @dev UDVT that represents a slot holding a int256.
   */
  type Int256Slot is bytes32;

  /**
   * @dev Cast an arbitrary slot to a Int256Slot.
   */
  function asInt256(bytes32 slot) internal pure returns (Int256Slot) {
    return Int256Slot.wrap(slot);
  }

  /**
   * @dev Load the value held at location `slot` in transient storage.
   */
  function tload(AddressSlot slot) internal view returns (address value) {
    assembly ('memory-safe') {
      value := tload(slot)
    }
  }

  /**
   * @dev Store `value` at location `slot` in transient storage.
   */
  function tstore(AddressSlot slot, address value) internal {
    assembly ('memory-safe') {
      tstore(slot, value)
    }
  }

  /**
   * @dev Load the value held at location `slot` in transient storage.
   */
  function tload(BooleanSlot slot) internal view returns (bool value) {
    assembly ('memory-safe') {
      value := tload(slot)
    }
  }

  /**
   * @dev Store `value` at location `slot` in transient storage.
   */
  function tstore(BooleanSlot slot, bool value) internal {
    assembly ('memory-safe') {
      tstore(slot, value)
    }
  }

  /**
   * @dev Load the value held at location `slot` in transient storage.
   */
  function tload(Bytes32Slot slot) internal view returns (bytes32 value) {
    assembly ('memory-safe') {
      value := tload(slot)
    }
  }

  /**
   * @dev Store `value` at location `slot` in transient storage.
   */
  function tstore(Bytes32Slot slot, bytes32 value) internal {
    assembly ('memory-safe') {
      tstore(slot, value)
    }
  }

  /**
   * @dev Load the value held at location `slot` in transient storage.
   */
  function tload(Uint256Slot slot) internal view returns (uint256 value) {
    assembly ('memory-safe') {
      value := tload(slot)
    }
  }

  /**
   * @dev Store `value` at location `slot` in transient storage.
   */
  function tstore(Uint256Slot slot, uint256 value) internal {
    assembly ('memory-safe') {
      tstore(slot, value)
    }
  }

  /**
   * @dev Load the value held at location `slot` in transient storage.
   */
  function tload(Int256Slot slot) internal view returns (int256 value) {
    assembly ('memory-safe') {
      value := tload(slot)
    }
  }

  /**
   * @dev Store `value` at location `slot` in transient storage.
   */
  function tstore(Int256Slot slot, int256 value) internal {
    assembly ('memory-safe') {
      tstore(slot, value)
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

// src/utils/ExtSload.sol

/// @title ExtSload
/// @author Aave Labs
/// @notice This allows the source contract to make its state available to external contracts.
abstract contract ExtSload is IExtSload {
  /// @inheritdoc IExtSload
  function extSload(bytes32 slot) external view returns (bytes32 ret) {
    assembly ('memory-safe') {
      ret := sload(slot)
    }
  }

  /// @inheritdoc IExtSload
  function extSloads(bytes32[] calldata slots) external view returns (bytes32[] memory) {
    // @dev we disregard solidity memory conventions since we take control of entire execution
    assembly {
      mstore(0x00, 0x20) // to abi-encode response, the array will be found at the next word
      mstore(0x20, slots.length) // set the length of dynamic array
      let start := 0x40 // start of the array
      let end := add(start, shl(5, slots.length))
      for {
        let input := slots.offset
      } lt(start, end) {
        start := add(start, 0x20)
      } {
        mstore(start, sload(calldataload(input)))
        input := add(input, 0x20)
      }
      return(0x00, end) // return abi-encoded dynamic array
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

// src/dependencies/openzeppelin/IERC2612.sol

// OpenZeppelin Contracts (last updated v5.4.0) (interfaces/IERC2612.sol)

interface IERC2612 is IERC20Permit {}

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

// tests/helpers/mocks/MockPriceFeed.sol

contract MockPriceFeed is IPriceFeed {
  uint8 public immutable override decimals;

  string public override description;

  int256 private _price;

  error OperationNotSupported();

  constructor(uint8 decimals_, string memory description_, uint256 price_) {
    decimals = decimals_;
    description = description_;
    _price = int256(price_);
  }

  function setPrice(uint256 price) external {
    _price = int256(price);
  }

  function latestAnswer() external view override returns (int256) {
    return _price;
  }
}

// src/utils/Multicall.sol

/// @title Multicall
/// @author Aave Labs
/// @notice This contract allows for batching multiple calls into a single call.
/// @dev Inspired by the OpenZeppelin Multicall contract.
abstract contract Multicall is IMulticall {
  /// @inheritdoc IMulticall
  function multicall(bytes[] calldata data) public virtual returns (bytes[] memory) {
    bytes[] memory results = new bytes[](data.length);
    for (uint256 i; i < data.length; ++i) {
      (bool ok, bytes memory res) = address(this).delegatecall(data[i]);

      assembly ('memory-safe') {
        if iszero(ok) {
          revert(add(res, 32), mload(res)) // bubble up first revert
        }
      }

      results[i] = res;
    }
    return results;
  }
}

// src/utils/NoncesKeyed.sol

/// @title NoncesKeyed
/// @author Aave Labs
/// @notice Provides tracking nonces for addresses. Supports keyed nonces, where nonces will only increment for each key.
/// @dev Follows the https://eips.ethereum.org/EIPS/eip-4337#semi-abstracted-nonce-support[ERC-4337's semi-abstracted nonce system].
/// @dev Inspired by the OpenZeppelin NoncesKeyed contract.
contract NoncesKeyed is INoncesKeyed {
  /// @custom:storage-location erc7201:aave-v4.storage.NoncesKeyed
  struct NoncesKeyedStorage {
    mapping(address owner => mapping(uint192 key => uint64 nonce)) _nonces;
  }

  /// @dev The storage slot for the NoncesKeyed storage struct.
  bytes32 private constant NAMESPACE_SLOT =
    // keccak256(abi.encode(uint256(keccak256("aave-v4.storage.NoncesKeyed")) - 1)) & ~bytes32(uint256(0xff))
    0x474d4a5585c1bae3dbeb574bb96408c7174aadd8ab635de4ab498e2723195f00;

  /// @inheritdoc INoncesKeyed
  function useNonce(uint192 key) external returns (uint256) {
    return _useNonce(msg.sender, key);
  }

  /// @inheritdoc INoncesKeyed
  function nonces(address owner, uint192 key) public view returns (uint256) {
    return _pack(key, _getNoncesKeyedStorage()._nonces[owner][key]);
  }

  /// @notice Consumes the next unused nonce for an address and key.
  /// @dev Returns the current packed `keyNonce`. Consumed nonce is increased, so calling this function twice
  /// with the same arguments will return different (sequential) results.
  function _useNonce(address owner, uint192 key) internal returns (uint256) {
    // For each account, the nonce has an initial value of 0, can only be incremented by one, and cannot be
    // decremented or reset. This guarantees that the nonce never overflows.
    unchecked {
      // It is important to do x++ and not ++x here.
      return _pack(key, _getNoncesKeyedStorage()._nonces[owner][key]++);
    }
  }

  /// @dev Same as `_useNonce` but checking that `nonce` is the next valid for `owner` for specified packed `keyNonce`.
  function _useCheckedNonce(address owner, uint256 keyNonce) internal {
    (uint192 key, ) = _unpack(keyNonce);
    uint256 current = _useNonce(owner, key);
    require(keyNonce == current, InvalidAccountNonce(owner, current));
  }

  /// @dev Pack key and nonce into a keyNonce.
  function _pack(uint192 key, uint64 nonce) private pure returns (uint256) {
    return (uint256(key) << 64) | nonce;
  }

  /// @dev Unpack a keyNonce into its key and nonce components.
  function _unpack(uint256 keyNonce) private pure returns (uint192 key, uint64 nonce) {
    return (uint192(keyNonce >> 64), uint64(keyNonce));
  }

  /// @dev Loads the NoncesKeyed storage struct.
  function _getNoncesKeyedStorage() private pure returns (NoncesKeyedStorage storage $) {
    assembly ('memory-safe') {
      $.slot := NAMESPACE_SLOT
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

// src/dependencies/openzeppelin/ReentrancyGuardTransient.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/ReentrancyGuardTransient.sol)

/**
 * @dev Variant of {ReentrancyGuard} that uses transient storage.
 *
 * NOTE: This variant only works on networks where EIP-1153 is available.
 *
 * _Available since v5.1._
 *
 * @custom:stateless
 */
abstract contract ReentrancyGuardTransient {
  using TransientSlot for *;

  // keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.ReentrancyGuard")) - 1)) & ~bytes32(uint256(0xff))
  bytes32 private constant REENTRANCY_GUARD_STORAGE =
    0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;

  /**
   * @dev Unauthorized reentrant call.
   */
  error ReentrancyGuardReentrantCall();

  /**
   * @dev Prevents a contract from calling itself, directly or indirectly.
   * Calling a `nonReentrant` function from another `nonReentrant`
   * function is not supported. It is possible to prevent this from happening
   * by making the `nonReentrant` function external, and making it call a
   * `private` function that does the actual work.
   */
  modifier nonReentrant() {
    _nonReentrantBefore();
    _;
    _nonReentrantAfter();
  }

  /**
   * @dev A `view` only version of {nonReentrant}. Use to block view functions
   * from being called, preventing reading from inconsistent contract state.
   *
   * CAUTION: This is a "view" modifier and does not change the reentrancy
   * status. Use it only on view functions. For payable or non-payable functions,
   * use the standard {nonReentrant} modifier instead.
   */
  modifier nonReentrantView() {
    _nonReentrantBeforeView();
    _;
  }

  function _nonReentrantBeforeView() private view {
    if (_reentrancyGuardEntered()) {
      revert ReentrancyGuardReentrantCall();
    }
  }

  function _nonReentrantBefore() private {
    // On the first call to nonReentrant, REENTRANCY_GUARD_STORAGE.asBoolean().tload() will be false
    _nonReentrantBeforeView();

    // Any calls to nonReentrant after this point will fail
    _reentrancyGuardStorageSlot().asBoolean().tstore(true);
  }

  function _nonReentrantAfter() private {
    _reentrancyGuardStorageSlot().asBoolean().tstore(false);
  }

  /**
   * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
   * `nonReentrant` function in the call stack.
   */
  function _reentrancyGuardEntered() internal view returns (bool) {
    return _reentrancyGuardStorageSlot().asBoolean().tload();
  }

  function _reentrancyGuardStorageSlot() internal pure virtual returns (bytes32) {
    return REENTRANCY_GUARD_STORAGE;
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

// src/dependencies/openzeppelin/IERC4626.sol

// OpenZeppelin Contracts (last updated v5.5.0) (interfaces/IERC4626.sol)

/**
 * @dev Interface of the ERC-4626 "Tokenized Vault Standard", as defined in
 * https://eips.ethereum.org/EIPS/eip-4626[ERC-4626].
 */
interface IERC4626 is IERC20, IERC20Metadata {
  event Deposit(address indexed sender, address indexed owner, uint256 assets, uint256 shares);

  event Withdraw(
    address indexed sender,
    address indexed receiver,
    address indexed owner,
    uint256 assets,
    uint256 shares
  );

  /**
   * @dev Returns the address of the underlying token used for the Vault for accounting, depositing, and withdrawing.
   *
   * - MUST be an ERC-20 token contract.
   * - MUST NOT revert.
   */
  function asset() external view returns (address assetTokenAddress);

  /**
   * @dev Returns the total amount of the underlying asset that is “managed” by Vault.
   *
   * - SHOULD include any compounding that occurs from yield.
   * - MUST be inclusive of any fees that are charged against assets in the Vault.
   * - MUST NOT revert.
   */
  function totalAssets() external view returns (uint256 totalManagedAssets);

  /**
   * @dev Returns the amount of shares that the Vault would exchange for the amount of assets provided, in an ideal
   * scenario where all the conditions are met.
   *
   * - MUST NOT be inclusive of any fees that are charged against assets in the Vault.
   * - MUST NOT show any variations depending on the caller.
   * - MUST NOT reflect slippage or other on-chain conditions, when performing the actual exchange.
   * - MUST NOT revert.
   *
   * NOTE: This calculation MAY NOT reflect the “per-user” price-per-share, and instead should reflect the
   * “average-user’s” price-per-share, meaning what the average user should expect to see when exchanging to and
   * from.
   */
  function convertToShares(uint256 assets) external view returns (uint256 shares);

  /**
   * @dev Returns the amount of assets that the Vault would exchange for the amount of shares provided, in an ideal
   * scenario where all the conditions are met.
   *
   * - MUST NOT be inclusive of any fees that are charged against assets in the Vault.
   * - MUST NOT show any variations depending on the caller.
   * - MUST NOT reflect slippage or other on-chain conditions, when performing the actual exchange.
   * - MUST NOT revert.
   *
   * NOTE: This calculation MAY NOT reflect the “per-user” price-per-share, and instead should reflect the
   * “average-user’s” price-per-share, meaning what the average user should expect to see when exchanging to and
   * from.
   */
  function convertToAssets(uint256 shares) external view returns (uint256 assets);

  /**
   * @dev Returns the maximum amount of the underlying asset that can be deposited into the Vault for the receiver,
   * through a deposit call.
   *
   * - MUST return a limited value if receiver is subject to some deposit limit.
   * - MUST return 2 ** 256 - 1 if there is no limit on the maximum amount of assets that may be deposited.
   * - MUST NOT revert.
   */
  function maxDeposit(address receiver) external view returns (uint256 maxAssets);

  /**
   * @dev Allows an on-chain or off-chain user to simulate the effects of their deposit at the current block, given
   * current on-chain conditions.
   *
   * - MUST return as close to and no more than the exact amount of Vault shares that would be minted in a deposit
   *   call in the same transaction. I.e. deposit should return the same or more shares as previewDeposit if called
   *   in the same transaction.
   * - MUST NOT account for deposit limits like those returned from maxDeposit and should always act as though the
   *   deposit would be accepted, regardless if the user has enough tokens approved, etc.
   * - MUST be inclusive of deposit fees. Integrators should be aware of the existence of deposit fees.
   * - MUST NOT revert.
   *
   * NOTE: any unfavorable discrepancy between convertToShares and previewDeposit SHOULD be considered slippage in
   * share price or some other type of condition, meaning the depositor will lose assets by depositing.
   */
  function previewDeposit(uint256 assets) external view returns (uint256 shares);

  /**
   * @dev Deposit `assets` underlying tokens and send the corresponding number of vault shares (`shares`) to `receiver`.
   *
   * - MUST emit the Deposit event.
   * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
   *   deposit execution, and are accounted for during deposit.
   * - MUST revert if all of assets cannot be deposited (due to deposit limit being reached, slippage, the user not
   *   approving enough underlying tokens to the Vault contract, etc).
   *
   * NOTE: most implementations will require pre-approval of the Vault with the Vault’s underlying asset token.
   */
  function deposit(uint256 assets, address receiver) external returns (uint256 shares);

  /**
   * @dev Returns the maximum amount of the Vault shares that can be minted for the receiver, through a mint call.
   * - MUST return a limited value if receiver is subject to some mint limit.
   * - MUST return 2 ** 256 - 1 if there is no limit on the maximum amount of shares that may be minted.
   * - MUST NOT revert.
   */
  function maxMint(address receiver) external view returns (uint256 maxShares);

  /**
   * @dev Allows an on-chain or off-chain user to simulate the effects of their mint at the current block, given
   * current on-chain conditions.
   *
   * - MUST return as close to and no fewer than the exact amount of assets that would be deposited in a mint call
   *   in the same transaction. I.e. mint should return the same or fewer assets as previewMint if called in the
   *   same transaction.
   * - MUST NOT account for mint limits like those returned from maxMint and should always act as though the mint
   *   would be accepted, regardless if the user has enough tokens approved, etc.
   * - MUST be inclusive of deposit fees. Integrators should be aware of the existence of deposit fees.
   * - MUST NOT revert.
   *
   * NOTE: any unfavorable discrepancy between convertToAssets and previewMint SHOULD be considered slippage in
   * share price or some other type of condition, meaning the depositor will lose assets by minting.
   */
  function previewMint(uint256 shares) external view returns (uint256 assets);

  /**
   * @dev Mints exactly `shares` vault shares to `receiver` in exchange for `assets` underlying tokens.
   *
   * - MUST emit the Deposit event.
   * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the mint
   *   execution, and are accounted for during mint.
   * - MUST revert if all of shares cannot be minted (due to deposit limit being reached, slippage, the user not
   *   approving enough underlying tokens to the Vault contract, etc).
   *
   * NOTE: most implementations will require pre-approval of the Vault with the Vault’s underlying asset token.
   */
  function mint(uint256 shares, address receiver) external returns (uint256 assets);

  /**
   * @dev Returns the maximum amount of the underlying asset that can be withdrawn from the owner balance in the
   * Vault, through a withdraw call.
   *
   * - MUST return a limited value if owner is subject to some withdrawal limit or timelock.
   * - MUST NOT revert.
   */
  function maxWithdraw(address owner) external view returns (uint256 maxAssets);

  /**
   * @dev Allows an on-chain or off-chain user to simulate the effects of their withdrawal at the current block,
   * given current on-chain conditions.
   *
   * - MUST return as close to and no fewer than the exact amount of Vault shares that would be burned in a withdraw
   *   call in the same transaction. I.e. withdraw should return the same or fewer shares as previewWithdraw if
   *   called
   *   in the same transaction.
   * - MUST NOT account for withdrawal limits like those returned from maxWithdraw and should always act as though
   *   the withdrawal would be accepted, regardless if the user has enough shares, etc.
   * - MUST be inclusive of withdrawal fees. Integrators should be aware of the existence of withdrawal fees.
   * - MUST NOT revert.
   *
   * NOTE: any unfavorable discrepancy between convertToShares and previewWithdraw SHOULD be considered slippage in
   * share price or some other type of condition, meaning the depositor will lose assets by depositing.
   */
  function previewWithdraw(uint256 assets) external view returns (uint256 shares);

  /**
   * @dev Burns shares from owner and sends exactly assets of underlying tokens to receiver.
   *
   * - MUST emit the Withdraw event.
   * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
   *   withdraw execution, and are accounted for during withdraw.
   * - MUST revert if all of assets cannot be withdrawn (due to withdrawal limit being reached, slippage, the owner
   *   not having enough shares, etc).
   *
   * Note that some implementations will require pre-requesting to the Vault before a withdrawal may be performed.
   * Those methods should be performed separately.
   */
  function withdraw(
    uint256 assets,
    address receiver,
    address owner
  ) external returns (uint256 shares);

  /**
   * @dev Returns the maximum amount of Vault shares that can be redeemed from the owner balance in the Vault,
   * through a redeem call.
   *
   * - MUST return a limited value if owner is subject to some withdrawal limit or timelock.
   * - MUST return balanceOf(owner) if owner is not subject to any withdrawal limit or timelock.
   * - MUST NOT revert.
   */
  function maxRedeem(address owner) external view returns (uint256 maxShares);

  /**
   * @dev Allows an on-chain or off-chain user to simulate the effects of their redemption at the current block,
   * given current on-chain conditions.
   *
   * - MUST return as close to and no more than the exact amount of assets that would be withdrawn in a redeem call
   *   in the same transaction. I.e. redeem should return the same or more assets as previewRedeem if called in the
   *   same transaction.
   * - MUST NOT account for redemption limits like those returned from maxRedeem and should always act as though the
   *   redemption would be accepted, regardless if the user has enough shares, etc.
   * - MUST be inclusive of withdrawal fees. Integrators should be aware of the existence of withdrawal fees.
   * - MUST NOT revert.
   *
   * NOTE: any unfavorable discrepancy between convertToAssets and previewRedeem SHOULD be considered slippage in
   * share price or some other type of condition, meaning the depositor will lose assets by redeeming.
   */
  function previewRedeem(uint256 shares) external view returns (uint256 assets);

  /**
   * @dev Burns exactly shares from owner and sends assets of underlying tokens to receiver.
   *
   * - MUST emit the Withdraw event.
   * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
   *   redeem execution, and are accounted for during redeem.
   * - MUST revert if all of shares cannot be redeemed (due to withdrawal limit being reached, slippage, the owner
   *   not having enough shares, etc).
   *
   * NOTE: some implementations will require pre-requesting to the Vault before a withdrawal may be performed.
   * Those methods should be performed separately.
   */
  function redeem(
    uint256 shares,
    address receiver,
    address owner
  ) external returns (uint256 assets);
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

// src/dependencies/openzeppelin/Bytes.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/Bytes.sol)

/**
 * @dev Bytes operations.
 */
library Bytes {
  /**
   * @dev Forward search for `s` in `buffer`
   * * If `s` is present in the buffer, returns the index of the first instance
   * * If `s` is not present in the buffer, returns type(uint256).max
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/indexOf[Javascript's `Array.indexOf`]
   */
  function indexOf(bytes memory buffer, bytes1 s) internal pure returns (uint256) {
    return indexOf(buffer, s, 0);
  }

  /**
   * @dev Forward search for `s` in `buffer` starting at position `pos`
   * * If `s` is present in the buffer (at or after `pos`), returns the index of the next instance
   * * If `s` is not present in the buffer (at or after `pos`), returns type(uint256).max
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/indexOf[Javascript's `Array.indexOf`]
   */
  function indexOf(bytes memory buffer, bytes1 s, uint256 pos) internal pure returns (uint256) {
    uint256 length = buffer.length;
    for (uint256 i = pos; i < length; ++i) {
      if (bytes1(_unsafeReadBytesOffset(buffer, i)) == s) {
        return i;
      }
    }
    return type(uint256).max;
  }

  /**
   * @dev Backward search for `s` in `buffer`
   * * If `s` is present in the buffer, returns the index of the last instance
   * * If `s` is not present in the buffer, returns type(uint256).max
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/lastIndexOf[Javascript's `Array.lastIndexOf`]
   */
  function lastIndexOf(bytes memory buffer, bytes1 s) internal pure returns (uint256) {
    return lastIndexOf(buffer, s, type(uint256).max);
  }

  /**
   * @dev Backward search for `s` in `buffer` starting at position `pos`
   * * If `s` is present in the buffer (at or before `pos`), returns the index of the previous instance
   * * If `s` is not present in the buffer (at or before `pos`), returns type(uint256).max
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/lastIndexOf[Javascript's `Array.lastIndexOf`]
   */
  function lastIndexOf(bytes memory buffer, bytes1 s, uint256 pos) internal pure returns (uint256) {
    unchecked {
      uint256 length = buffer.length;
      for (uint256 i = Math.min(Math.saturatingAdd(pos, 1), length); i > 0; --i) {
        if (bytes1(_unsafeReadBytesOffset(buffer, i - 1)) == s) {
          return i - 1;
        }
      }
      return type(uint256).max;
    }
  }

  /**
   * @dev Copies the content of `buffer`, from `start` (included) to the end of `buffer` into a new bytes object in
   * memory.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(bytes memory buffer, uint256 start) internal pure returns (bytes memory) {
    return slice(buffer, start, buffer.length);
  }

  /**
   * @dev Copies the content of `buffer`, from `start` (included) to `end` (excluded) into a new bytes object in
   * memory. The `end` argument is truncated to the length of the `buffer`.
   *
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
   */
  function slice(
    bytes memory buffer,
    uint256 start,
    uint256 end
  ) internal pure returns (bytes memory) {
    // sanitize
    end = Math.min(end, buffer.length);
    start = Math.min(start, end);

    // allocate and copy
    bytes memory result = new bytes(end - start);
    assembly ('memory-safe') {
      mcopy(add(result, 0x20), add(add(buffer, 0x20), start), sub(end, start))
    }

    return result;
  }

  /**
   * @dev Moves the content of `buffer`, from `start` (included) to the end of `buffer` to the start of that buffer.
   *
   * NOTE: This function modifies the provided buffer in place. If you need to preserve the original buffer, use {slice} instead
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(bytes memory buffer, uint256 start) internal pure returns (bytes memory) {
    return splice(buffer, start, buffer.length);
  }

  /**
   * @dev Moves the content of `buffer`, from `start` (included) to end (excluded) to the start of that buffer. The
   * `end` argument is truncated to the length of the `buffer`.
   *
   * NOTE: This function modifies the provided buffer in place. If you need to preserve the original buffer, use {slice} instead
   * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/splice[Javascript's `Array.splice`]
   */
  function splice(
    bytes memory buffer,
    uint256 start,
    uint256 end
  ) internal pure returns (bytes memory) {
    // sanitize
    end = Math.min(end, buffer.length);
    start = Math.min(start, end);

    // allocate and copy
    assembly ('memory-safe') {
      mcopy(add(buffer, 0x20), add(add(buffer, 0x20), start), sub(end, start))
      mstore(buffer, sub(end, start))
    }

    return buffer;
  }

  /**
   * @dev Concatenate an array of bytes into a single bytes object.
   *
   * For fixed bytes types, we recommend using the solidity built-in `bytes.concat` or (equivalent)
   * `abi.encodePacked`.
   *
   * NOTE: this could be done in assembly with a single loop that expands starting at the FMP, but that would be
   * significantly less readable. It might be worth benchmarking the savings of the full-assembly approach.
   */
  function concat(bytes[] memory buffers) internal pure returns (bytes memory) {
    uint256 length = 0;
    for (uint256 i = 0; i < buffers.length; ++i) {
      length += buffers[i].length;
    }

    bytes memory result = new bytes(length);

    uint256 offset = 0x20;
    for (uint256 i = 0; i < buffers.length; ++i) {
      bytes memory input = buffers[i];
      assembly ('memory-safe') {
        mcopy(add(result, offset), add(input, 0x20), mload(input))
      }
      unchecked {
        offset += input.length;
      }
    }

    return result;
  }

  /**
   * @dev Returns true if the two byte buffers are equal.
   */
  function equal(bytes memory a, bytes memory b) internal pure returns (bool) {
    return a.length == b.length && keccak256(a) == keccak256(b);
  }

  /**
   * @dev Reverses the byte order of a bytes32 value, converting between little-endian and big-endian.
   * Inspired by https://graphics.stanford.edu/~seander/bithacks.html#ReverseParallel[Reverse Parallel]
   */
  function reverseBytes32(bytes32 value) internal pure returns (bytes32) {
    value = // swap bytes
      ((value >> 8) & 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF) |
      ((value & 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF) << 8);
    value = // swap 2-byte long pairs
      ((value >> 16) & 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF) |
      ((value & 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF) << 16);
    value = // swap 4-byte long pairs
      ((value >> 32) & 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF) |
      ((value & 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF) << 32);
    value = // swap 8-byte long pairs
      ((value >> 64) & 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF) |
      ((value & 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF) << 64);
    return (value >> 128) | (value << 128); // swap 16-byte long pairs
  }

  /// @dev Same as {reverseBytes32} but optimized for 128-bit values.
  function reverseBytes16(bytes16 value) internal pure returns (bytes16) {
    value = // swap bytes
      ((value & 0xFF00FF00FF00FF00FF00FF00FF00FF00) >> 8) |
      ((value & 0x00FF00FF00FF00FF00FF00FF00FF00FF) << 8);
    value = // swap 2-byte long pairs
      ((value & 0xFFFF0000FFFF0000FFFF0000FFFF0000) >> 16) |
      ((value & 0x0000FFFF0000FFFF0000FFFF0000FFFF) << 16);
    value = // swap 4-byte long pairs
      ((value & 0xFFFFFFFF00000000FFFFFFFF00000000) >> 32) |
      ((value & 0x00000000FFFFFFFF00000000FFFFFFFF) << 32);
    return (value >> 64) | (value << 64); // swap 8-byte long pairs
  }

  /// @dev Same as {reverseBytes32} but optimized for 64-bit values.
  function reverseBytes8(bytes8 value) internal pure returns (bytes8) {
    value = ((value & 0xFF00FF00FF00FF00) >> 8) | ((value & 0x00FF00FF00FF00FF) << 8); // swap bytes
    value = ((value & 0xFFFF0000FFFF0000) >> 16) | ((value & 0x0000FFFF0000FFFF) << 16); // swap 2-byte long pairs
    return (value >> 32) | (value << 32); // swap 4-byte long pairs
  }

  /// @dev Same as {reverseBytes32} but optimized for 32-bit values.
  function reverseBytes4(bytes4 value) internal pure returns (bytes4) {
    value = ((value & 0xFF00FF00) >> 8) | ((value & 0x00FF00FF) << 8); // swap bytes
    return (value >> 16) | (value << 16); // swap 2-byte long pairs
  }

  /// @dev Same as {reverseBytes32} but optimized for 16-bit values.
  function reverseBytes2(bytes2 value) internal pure returns (bytes2) {
    return (value >> 8) | (value << 8);
  }

  /**
   * @dev Counts the number of leading zero bits a bytes array. Returns `8 * buffer.length`
   * if the buffer is all zeros.
   */
  function clz(bytes memory buffer) internal pure returns (uint256) {
    for (uint256 i = 0; i < buffer.length; i += 0x20) {
      bytes32 chunk = _unsafeReadBytesOffset(buffer, i);
      if (chunk != bytes32(0)) {
        return Math.min(8 * i + Math.clz(uint256(chunk)), 8 * buffer.length);
      }
    }
    return 8 * buffer.length;
  }

  /**
   * @dev Reads a bytes32 from a bytes array without bounds checking.
   *
   * NOTE: making this function internal would mean it could be used with memory unsafe offset, and marking the
   * assembly block as such would prevent some optimizations.
   */
  function _unsafeReadBytesOffset(
    bytes memory buffer,
    uint256 offset
  ) private pure returns (bytes32 value) {
    // This is not memory safe in the general case, but all calls to this private function are within bounds.
    assembly ('memory-safe') {
      value := mload(add(add(buffer, 0x20), offset))
    }
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

// src/spoke/interfaces/ITokenizationSpoke.sol

/// @title ITokenizationSpoke
/// @author Aave Labs
interface ITokenizationSpoke is IERC4626, IERC2612, IIntentConsumer {
  /// @notice Intent data to deposit assets into the TokenizationSpoke.
  /// @param depositor The address of the user depositing assets.
  /// @param assets The amount of assets to deposit.
  /// @param receiver The address that will receive the minted shares.
  /// @param nonce The key-prefixed nonce for the signature.
  /// @param deadline The deadline for the intent.
  struct TokenizedDeposit {
    address depositor;
    uint256 assets;
    address receiver;
    uint256 nonce;
    uint256 deadline;
  }

  /// @notice Intent data to mint shares from the TokenizationSpoke.
  /// @param depositor The address of the user depositing assets.
  /// @param shares The amount of shares to mint.
  /// @param receiver The address that will receive the minted shares.
  /// @param nonce The key-prefixed nonce for the signature.
  /// @param deadline The deadline for the intent.
  struct TokenizedMint {
    address depositor;
    uint256 shares;
    address receiver;
    uint256 nonce;
    uint256 deadline;
  }

  /// @notice Intent data to withdraw assets from the TokenizationSpoke.
  /// @param owner The address of the user withdrawing assets.
  /// @param assets The amount of assets to withdraw.
  /// @param receiver The address that will receive the withdrawn assets.
  /// @param nonce The key-prefixed nonce for the signature.
  /// @param deadline The deadline for the intent.
  struct TokenizedWithdraw {
    address owner;
    uint256 assets;
    address receiver;
    uint256 nonce;
    uint256 deadline;
  }

  /// @notice Intent data to redeem shares from the TokenizationSpoke.
  /// @param owner The address of the user redeeming shares.
  /// @param shares The amount of shares to redeem.
  /// @param receiver The address that will receive the redeemed assets.
  /// @param nonce The key-prefixed nonce for the signature.
  /// @param deadline The deadline for the intent.
  struct TokenizedRedeem {
    address owner;
    uint256 shares;
    address receiver;
    uint256 nonce;
    uint256 deadline;
  }

  /// @notice Emitted when the immutable variables of the TokenizationSpoke are set.
  /// @param hub The address of the Hub.
  /// @param assetId The identifier of the asset.
  event SetTokenizationSpokeImmutables(address indexed hub, uint256 indexed assetId);

  /// @notice Deposits assets into the TokenizationSpoke with a signature.
  /// @dev Uses keyed-nonces where for each key's namespace nonce is consumed sequentially.
  /// @param params The parameters for the deposit.
  /// @param signature The EIP712-typed signed bytes for the deposit.
  /// @return The amount of shares minted.
  function depositWithSig(
    TokenizedDeposit calldata params,
    bytes calldata signature
  ) external returns (uint256);

  /// @notice Mints shares of the TokenizationSpoke with a signature.
  /// @dev Uses keyed-nonces where for each key's namespace nonce is consumed sequentially.
  /// @param params The parameters for the mint.
  /// @param signature The EIP712-typed signed bytes for the mint.
  /// @return The amount of assets deposited.
  function mintWithSig(
    TokenizedMint calldata params,
    bytes calldata signature
  ) external returns (uint256);

  /// @notice Withdraws assets from the TokenizationSpoke with a signature.
  /// @dev Uses keyed-nonces where for each key's namespace nonce is consumed sequentially.
  /// @param params The parameters for the withdraw.
  /// @param signature The EIP712-typed signed bytes for the withdraw.
  /// @return The amount of shares burnt.
  function withdrawWithSig(
    TokenizedWithdraw calldata params,
    bytes calldata signature
  ) external returns (uint256);

  /// @notice Redeems shares from the TokenizationSpoke with a signature.
  /// @dev Uses keyed-nonces where for each key's namespace nonce is consumed sequentially.
  /// @param params The parameters for the redeem.
  /// @param signature The EIP712-typed signed bytes for the redeem.
  /// @return The amount of assets burnt.
  function redeemWithSig(
    TokenizedRedeem calldata params,
    bytes calldata signature
  ) external returns (uint256);

  /// @notice Deposits assets into the vault with an underlying asset ERC2612-typed permit.
  /// @param assets The amount of assets to deposit.
  /// @param receiver The receiver of the shares.
  /// @param deadline The deadline of the permit.
  /// @param v The v value of the permit.
  /// @param r The r value of the permit.
  /// @param s The s value of the permit.
  /// @return The amount of shares minted.
  function depositWithPermit(
    uint256 assets,
    address receiver,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) external returns (uint256);

  /// @notice Sets approval for `spender` to spend `owner`'s share tokens via EIP712-typed signature.
  /// @dev Uses keyed-nonces where the share token permit nonce is consumed sequentially and key namespace is always set to `PERMIT_NONCE_NAMESPACE`.
  /// @dev Implements EIP-2612 permit functionality for the vault share token.
  /// @param owner The address of the token owner granting approval.
  /// @param spender The address being granted approval to spend tokens.
  /// @param value The amount of tokens approved for spending.
  /// @param deadline The timestamp by which the permit must be used.
  /// @param v The recovery byte of the signature.
  /// @param r The first 32 bytes of the signature.
  /// @param s The second 32 bytes of the signature.
  function permit(
    address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) external;

  /// @notice Revokes the current PERMIT_NAMESPACE_NONCE of caller & increments the nonce at this key.
  /// @return The consumed keyed-nonce.
  function usePermitNonce() external returns (uint256);

  /// @notice Resets the allowance of an owner for the caller.
  /// @param owner The owner of the allowance to renounce.
  function renounceAllowance(address owner) external;

  /// @notice Returns the address of the associated Hub.
  function hub() external view returns (address);

  /// @notice Returns the identifier of the associated asset.
  function assetId() external view returns (uint256);

  /// @notice Returns the maximum allowed spoke cap.
  function MAX_ALLOWED_SPOKE_CAP() external view returns (uint40);

  /// @notice Returns the nonce namespace for share token EIP-2612 permit signatures.
  /// @dev Share token permits strictly use this dedicated namespace in the keyed-nonce system as the nonce key.
  /// @dev Other vault intent operations can also use the this namespace as the nonce key.
  function PERMIT_NONCE_NAMESPACE() external pure returns (uint192);

  /// @notice Returns the type hash for the deposit intent.
  function DEPOSIT_TYPEHASH() external pure returns (bytes32);

  /// @notice Returns the type hash for the mint intent.
  function MINT_TYPEHASH() external pure returns (bytes32);

  /// @notice Returns the type hash for the withdraw intent.
  function WITHDRAW_TYPEHASH() external pure returns (bytes32);

  /// @notice Returns the type hash for the redeem intent.
  function REDEEM_TYPEHASH() external pure returns (bytes32);

  /// @notice Returns the type hash for the share token permit intent.
  function PERMIT_TYPEHASH() external pure returns (bytes32);

  /// @notice Returns the EIP-712 domain separator.
  function DOMAIN_SEPARATOR()
    external
    view
    override(IERC20Permit, IIntentConsumer)
    returns (bytes32);
}

// src/spoke/libraries/KeyValueList.sol

/// @title KeyValueList Library
/// @author Aave Labs
/// @notice Library to pack key-value pairs in a list.
/// @dev The `sortByKey` helper sorts by ascending order of the `key` & in case of collision by descending order of the `value`.
/// @dev This is achieved by sorting the packed `key-value` pair in descending order, but storing the invert of the `key` (ie `MAX_KEY - key`).
/// @dev Uninitialized keys are returned as (key: 0, value: 0) and are placed at the end of the list after sorting.
library KeyValueList {
  using Arrays for uint256[];
  using KeyValueList for *;

  /// @notice Thrown when adding a key which can't be stored in `KEY_BITS` or value in `VALUE_BITS`.
  error MaxDataSizeExceeded();

  /// @notice Container for packed key value dynamic list.
  struct List {
    uint256[] _inner;
  }

  uint256 internal constant KEY_BITS = 32;
  uint256 internal constant VALUE_BITS = 224;
  uint256 internal constant MAX_KEY = (1 << KEY_BITS) - 1;
  uint256 internal constant MAX_VALUE = (1 << VALUE_BITS) - 1;
  uint256 internal constant KEY_SHIFT = 256 - KEY_BITS;

  /// @notice Allocates memory for a KeyValue list of `size` elements.
  function init(uint256 size) internal pure returns (List memory) {
    return List(new uint256[](size));
  }

  /// @notice Returns the length of the list.
  function length(List memory self) internal pure returns (uint256) {
    return self._inner.length;
  }

  /// @notice Inserts packed `key`, `value` at `idx`. Reverts if data exceeds maximum allowed size.
  /// @dev Reverts if `key` equals or exceeds the `MAX_KEY` value and reverts if `value` equals or exceeds the `MAX_VALUE` value.
  function add(List memory self, uint256 idx, uint256 key, uint256 value) internal pure {
    require(key < MAX_KEY && value < MAX_VALUE, MaxDataSizeExceeded());
    self._inner[idx] = pack(key, value);
  }

  /// @notice Returns the key-value pair at the given index.
  /// @dev Uninitialized keys are returned as (key: 0, value: 0).
  function get(List memory self, uint256 idx) internal pure returns (uint256, uint256) {
    return self._inner[idx].unpack();
  }

  /// @notice Returns the key-value pair at the given index without bounds checking.
  /// @dev Uninitialized keys are returned as (key: 0, value: 0).
  function uncheckedAt(List memory self, uint256 idx) internal pure returns (uint256, uint256) {
    return self._inner.unsafeMemoryAccess(idx).unpack();
  }

  /// @notice Sorts the list in-place by ascending order of `key`, and descending order of `value` on collision.
  /// @dev All uninitialized keys are placed at the end of the list after sorting.
  /// @dev Since `key` is in the MSB, we can sort by the key by sorting the array in descending order
  /// (so the keys are in ascending order when unpacking, due to the inversion when packed).
  function sortByKey(List memory self) internal pure {
    self._inner.sort(gtComparator);
  }

  /// @notice Packs a given `key`, `value` pair into a single word.
  /// @dev Bound checks are expected to be done before packing.
  function pack(uint256 key, uint256 value) internal pure returns (uint256) {
    return ((MAX_KEY - key) << KEY_SHIFT) | value;
  }

  /// @notice Unpacks `key` from a previously packed word containing `key` and `value`.
  /// @dev The key is stored in the most significant bits of the word.
  function unpackKey(uint256 data) internal pure returns (uint256) {
    unchecked {
      return MAX_KEY - (data >> KEY_SHIFT);
    }
  }

  /// @notice Unpacks `value` from a previously packed word containing `key` and `value`.
  /// @dev The value is stored in the least significant bits of the word.
  function unpackValue(uint256 data) internal pure returns (uint256) {
    return data & ((1 << KEY_SHIFT) - 1);
  }

  /// @notice Unpacks both `key` and `value` from a previously packed word containing `key` and `value`.
  /// @dev Uninitialized keys are returned as (key: 0, value: 0).
  /// @param data The packed word containing `key` and `value`.
  function unpack(uint256 data) internal pure returns (uint256, uint256) {
    if (data == 0) return (0, 0);
    return (data.unpackKey(), data.unpackValue());
  }

  /// @notice Comparator function performing greater-than comparison.
  /// @return True if `a` is greater than `b`.
  function gtComparator(uint256 a, uint256 b) internal pure returns (bool) {
    return a > b;
  }
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

// src/dependencies/openzeppelin/SignatureChecker.sol

// OpenZeppelin Contracts (last updated v5.5.0) (utils/cryptography/SignatureChecker.sol)

/**
 * @dev Signature verification helper that can be used instead of `ECDSA.recover` to seamlessly support:
 *
 * * ECDSA signatures from externally owned accounts (EOAs)
 * * ERC-1271 signatures from smart contract wallets like Argent and Safe Wallet (previously Gnosis Safe)
 * * ERC-7913 signatures from keys that do not have an Ethereum address of their own
 *
 * See https://eips.ethereum.org/EIPS/eip-1271[ERC-1271] and https://eips.ethereum.org/EIPS/eip-7913[ERC-7913].
 */
library SignatureChecker {
  using Bytes for bytes;

  /**
   * @dev Checks if a signature is valid for a given signer and data hash. If the signer has code, the
   * signature is validated against it using ERC-1271, otherwise it's validated using `ECDSA.recover`.
   *
   * NOTE: Unlike ECDSA signatures, contract signatures are revocable, and the outcome of this function can thus
   * change through time. It could return true at block N and false at block N+1 (or the opposite).
   *
   * NOTE: For an extended version of this function that supports ERC-7913 signatures, see {isValidSignatureNow-bytes-bytes32-bytes-}.
   */
  function isValidSignatureNow(
    address signer,
    bytes32 hash,
    bytes memory signature
  ) internal view returns (bool) {
    if (signer.code.length == 0) {
      (address recovered, ECDSA.RecoverError err, ) = ECDSA.tryRecover(hash, signature);
      return err == ECDSA.RecoverError.NoError && recovered == signer;
    } else {
      return isValidERC1271SignatureNow(signer, hash, signature);
    }
  }

  /**
   * @dev Variant of {isValidSignatureNow} that takes a signature in calldata
   */
  function isValidSignatureNowCalldata(
    address signer,
    bytes32 hash,
    bytes calldata signature
  ) internal view returns (bool) {
    if (signer.code.length == 0) {
      (address recovered, ECDSA.RecoverError err, ) = ECDSA.tryRecoverCalldata(hash, signature);
      return err == ECDSA.RecoverError.NoError && recovered == signer;
    } else {
      return isValidERC1271SignatureNow(signer, hash, signature);
    }
  }

  /**
   * @dev Checks if a signature is valid for a given signer and data hash. The signature is validated
   * against the signer smart contract using ERC-1271.
   *
   * NOTE: Unlike ECDSA signatures, contract signatures are revocable, and the outcome of this function can thus
   * change through time. It could return true at block N and false at block N+1 (or the opposite).
   */
  function isValidERC1271SignatureNow(
    address signer,
    bytes32 hash,
    bytes memory signature
  ) internal view returns (bool result) {
    bytes4 selector = IERC1271.isValidSignature.selector;
    uint256 length = signature.length;

    assembly ('memory-safe') {
      // Encoded calldata is :
      // [ 0x00 - 0x03 ] <selector>
      // [ 0x04 - 0x23 ] <hash>
      // [ 0x24 - 0x44 ] <signature offset> (0x40)
      // [ 0x44 - 0x64 ] <signature length>
      // [ 0x64 - ...  ] <signature data>
      let ptr := mload(0x40)
      mstore(ptr, selector)
      mstore(add(ptr, 0x04), hash)
      mstore(add(ptr, 0x24), 0x40)
      mcopy(add(ptr, 0x44), signature, add(length, 0x20))

      let success := staticcall(gas(), signer, ptr, add(length, 0x64), 0x00, 0x20)
      result := and(success, and(gt(returndatasize(), 0x1f), eq(mload(0x00), selector)))
    }
  }

  /**
   * @dev Verifies a signature for a given ERC-7913 signer and hash.
   *
   * The signer is a `bytes` object that is the concatenation of an address and optionally a key:
   * `verifier || key`. A signer must be at least 20 bytes long.
   *
   * Verification is done as follows:
   *
   * * If `signer.length < 20`: verification fails
   * * If `signer.length == 20`: verification is done using {isValidSignatureNow}
   * * Otherwise: verification is done using {IERC7913SignatureVerifier}
   *
   * NOTE: Unlike ECDSA signatures, contract signatures are revocable, and the outcome of this function can thus
   * change through time. It could return true at block N and false at block N+1 (or the opposite).
   */
  function isValidSignatureNow(
    bytes memory signer,
    bytes32 hash,
    bytes memory signature
  ) internal view returns (bool) {
    if (signer.length < 20) {
      return false;
    } else if (signer.length == 20) {
      return isValidSignatureNow(address(bytes20(signer)), hash, signature);
    } else {
      (bool success, bytes memory result) = address(bytes20(signer)).staticcall(
        abi.encodeCall(IERC7913SignatureVerifier.verify, (signer.slice(20), hash, signature))
      );
      return (success &&
        result.length >= 32 &&
        abi.decode(result, (bytes32)) == bytes32(IERC7913SignatureVerifier.verify.selector));
    }
  }

  /**
   * @dev Verifies multiple ERC-7913 `signatures` for a given `hash` using a set of `signers`.
   * Returns `false` if the number of signers and signatures is not the same.
   *
   * The signers should be ordered by their `keccak256` hash to ensure efficient duplication check. Unordered
   * signers are supported, but the uniqueness check will be more expensive.
   *
   * NOTE: Unlike ECDSA signatures, contract signatures are revocable, and the outcome of this function can thus
   * change through time. It could return true at block N and false at block N+1 (or the opposite).
   */
  function areValidSignaturesNow(
    bytes32 hash,
    bytes[] memory signers,
    bytes[] memory signatures
  ) internal view returns (bool) {
    if (signers.length != signatures.length) return false;

    bytes32 lastId = bytes32(0);

    for (uint256 i = 0; i < signers.length; ++i) {
      bytes memory signer = signers[i];

      // If one of the signatures is invalid, reject the batch
      if (!isValidSignatureNow(signer, hash, signatures[i])) return false;

      bytes32 id = keccak256(signer);
      // If the current signer ID is greater than all previous IDs, then this is a new signer.
      if (lastId < id) {
        lastId = id;
      } else {
        // If this signer id is not greater than all the previous ones, verify that it is not a duplicate of a previous one
        // This loop is never executed if the signers are ordered by id.
        for (uint256 j = 0; j < i; ++j) {
          if (id == keccak256(signers[j])) return false;
        }
      }
    }

    return true;
  }
}

// src/spoke/SpokeStorage.sol

/// @title SpokeStorage
/// @author Aave Labs
/// @notice Storage layout for the Spoke contract.
/// @dev This contract defines all storage variables used by Spoke.
abstract contract SpokeStorage {
  /// @dev Number of reserves listed in the Spoke.
  uint256 internal _reserveCount;

  /// @dev Liquidation configuration for the Spoke.
  ISpoke.LiquidationConfig internal _liquidationConfig;

  /// @dev Map of reserve identifiers to their Reserve data.
  mapping(uint256 reserveId => ISpoke.Reserve) internal _reserves;

  /// @dev Map of hub addresses and asset identifiers to the reserve identifier.
  mapping(address hub => mapping(uint256 assetId => uint256 reserveId))
    internal _hubAssetIdToReserveId;

  /// @dev Map of reserve identifiers and dynamic configuration keys to the dynamic configuration data.
  mapping(uint256 reserveId => mapping(uint32 dynamicConfigKey => ISpoke.DynamicReserveConfig))
    internal _dynamicConfig;

  /// @dev Map of user addresses to their position status.
  mapping(address user => ISpoke.PositionStatus) internal _positionStatus;

  /// @dev Map of user addresses and reserve identifiers to user positions.
  mapping(address user => mapping(uint256 reserveId => ISpoke.UserPosition))
    internal _userPositions;

  /// @dev Map of position manager addresses to their configuration data.
  mapping(address positionManager => ISpoke.PositionManagerConfig) internal _positionManager;

  /// @dev Reserved storage space to allow for future layout updates.
  uint256[50] private __gap;
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

// src/spoke/AaveOracle.sol

/// @title AaveOracle
/// @author Aave Labs
/// @notice Provides reserve prices.
/// @dev Oracles are spoke-specific, due to the usage of reserve id as index of the `_sources` mapping.
contract AaveOracle is IAaveOracle {
  /// @dev The number of decimals for the oracle.
  uint8 private immutable DECIMALS;

  /// @dev The address of the deployer.
  address private immutable DEPLOYER;

  /// @inheritdoc IPriceOracle
  address public spoke;

  /// @dev Map of reserve identifiers to their price feed.
  mapping(uint256 reserveId => IPriceFeed) internal _sources;

  /// @dev Constructor.
  /// @dev `decimals` must match the Spoke's decimals for compatibility.
  /// @param decimals_ The number of decimals for the oracle.
  constructor(uint8 decimals_) {
    DEPLOYER = msg.sender;
    DECIMALS = decimals_;
  }

  /// @inheritdoc IAaveOracle
  function setSpoke(address spoke_) external {
    require(msg.sender == DEPLOYER, OnlyDeployer());
    require(spoke_ != address(0), InvalidAddress());
    require(spoke == address(0), SpokeAlreadySet());
    require(ISpoke(spoke_).ORACLE() == address(this), OracleMismatch());
    spoke = spoke_;
    emit SetSpoke(spoke_);
  }

  /// @inheritdoc IAaveOracle
  function setReserveSource(uint256 reserveId, address source) external {
    require(msg.sender == spoke, OnlySpoke());
    IPriceFeed targetSource = IPriceFeed(source);
    require(targetSource.decimals() == DECIMALS, InvalidSourceDecimals(reserveId));
    _sources[reserveId] = targetSource;
    _getSourcePrice(reserveId);
    emit UpdateReserveSource(reserveId, source);
  }

  /// @inheritdoc IPriceOracle
  function decimals() external view returns (uint8) {
    return DECIMALS;
  }

  /// @inheritdoc IPriceOracle
  function getReservePrice(uint256 reserveId) external view returns (uint256) {
    return _getSourcePrice(reserveId);
  }

  /// @inheritdoc IAaveOracle
  function getReservesPrices(
    uint256[] calldata reserveIds
  ) external view returns (uint256[] memory) {
    uint256[] memory prices = new uint256[](reserveIds.length);
    for (uint256 i = 0; i < reserveIds.length; ++i) {
      prices[i] = _getSourcePrice(reserveIds[i]);
    }
    return prices;
  }

  /// @inheritdoc IAaveOracle
  function getReserveSource(uint256 reserveId) external view returns (address) {
    return address(_sources[reserveId]);
  }

  /// @dev Price of zero will revert with `InvalidPrice`.
  function _getSourcePrice(uint256 reserveId) internal view returns (uint256) {
    IPriceFeed source = _sources[reserveId];
    require(address(source) != address(0), InvalidSource(reserveId));

    int256 price = source.latestAnswer();
    require(price > 0, InvalidPrice(reserveId));

    return uint256(price);
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

// src/utils/IntentConsumer.sol

/// @title IntentConsumer
/// @author Aave Labs
/// @notice Base contract to consume EIP712-signed intents with keyed-nonces.
/// @dev The `_domainNameAndVersion()` function must be implemented to specify the EIP712 domain name and version.
/// @dev Implements ERC-5267 with `address(this)` as verifyingContract and no custom extensions or optional EIP-712 salt.
abstract contract IntentConsumer is IIntentConsumer, NoncesKeyed, EIP712 {
  /// @inheritdoc IIntentConsumer
  function DOMAIN_SEPARATOR() external view virtual returns (bytes32) {
    return _domainSeparator();
  }

  /// @dev Verifies the signature of an EIP712-typed intent and consumes its associated keyed-nonce.
  /// @param signer The address of the user.
  /// @param intentHash The hash of the intent struct.
  /// @param nonce The keyed-nonce for the intent.
  /// @param deadline The deadline timestamp for the intent.
  /// @param signature The signature bytes.
  function _verifyAndConsumeIntent(
    address signer,
    bytes32 intentHash,
    uint256 nonce,
    uint256 deadline,
    bytes calldata signature
  ) internal {
    require(block.timestamp <= deadline, InvalidSignature());
    bytes32 digest = _hashTypedData(intentHash);
    require(
      SignatureChecker.isValidSignatureNowCalldata(signer, digest, signature),
      InvalidSignature()
    );
    _useCheckedNonce(signer, nonce);
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

// src/spoke/libraries/EIP712Hash.sol

/// @title EIP712Hash library
/// @author Aave Labs
/// @notice Helper methods to hash EIP712 typed data structs.
library EIP712Hash {
  using EIP712Hash for *;

  bytes32 public constant SET_USER_POSITION_MANAGERS_TYPEHASH =
    // keccak256('SetUserPositionManagers(address onBehalfOf,PositionManagerUpdate[] updates,uint256 nonce,uint256 deadline)PositionManagerUpdate(address positionManager,bool approve)')
    0xba01f7bf3d3674c63670ec4a78b0d56aac1ad6e8c84468920b9e61bfe0b9851a;

  bytes32 public constant POSITION_MANAGER_UPDATE =
    // keccak256('PositionManagerUpdate(address positionManager,bool approve)')
    0x187dbd227227274b90655fb4011fc21dd749e8966fc040bd91e0b92609202565;

  bytes32 public constant TOKENIZED_DEPOSIT_TYPEHASH =
    // keccak256('TokenizedDeposit(address depositor,uint256 assets,address receiver,uint256 nonce,uint256 deadline)')
    0xdecc632fabbd6d9f578203db4396740eb2d81cf0fd7681b726d116e49cbc240c;

  bytes32 public constant TOKENIZED_MINT_TYPEHASH =
    // keccak256('TokenizedMint(address depositor,uint256 shares,address receiver,uint256 nonce,uint256 deadline)')
    0x12737e595645af6fb99e7985f3dff6fb716ac1ec517c0d2b21313985dc207343;

  bytes32 public constant TOKENIZED_WITHDRAW_TYPEHASH =
    // keccak256('TokenizedWithdraw(address owner,uint256 assets,address receiver,uint256 nonce,uint256 deadline)')
    0xe81b79af873473ec5cb79baa56499159fca87ff2e3333f24183127408a14acb5;

  bytes32 public constant TOKENIZED_REDEEM_TYPEHASH =
    // keccak256('TokenizedRedeem(address owner,uint256 shares,address receiver,uint256 nonce,uint256 deadline)')
    0x03929148275eed00e4c3ef9c0ee72e49ec6cb96c7a34941708e052f9a511334e;

  bytes32 public constant PERMIT_TYPEHASH =
    // keccak256('Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)')
    0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9;

  function hash(ISpoke.SetUserPositionManagers calldata params) internal pure returns (bytes32) {
    bytes32[] memory updatesHashes = new bytes32[](params.updates.length);
    for (uint256 i = 0; i < updatesHashes.length; ++i) {
      updatesHashes[i] = params.updates[i].hash();
    }
    return
      keccak256(
        abi.encode(
          SET_USER_POSITION_MANAGERS_TYPEHASH,
          params.onBehalfOf,
          keccak256(abi.encodePacked(updatesHashes)),
          params.nonce,
          params.deadline
        )
      );
  }

  function hash(
    ISpoke.PositionManagerUpdate calldata params
  ) internal pure returns (bytes32 digest) {
    // equivalent to: keccak256(abi.encode(POSITION_MANAGER_UPDATE, params.positionManager, params.approve))
    assembly {
      let fmp := mload(0x40)
      mstore(0, POSITION_MANAGER_UPDATE)
      mstore(0x20, shr(96, shl(96, calldataload(params)))) // params.positionManager
      mstore(0x40, iszero(iszero(calldataload(add(params, 0x20))))) // params.approve
      digest := keccak256(0, 0x60)
      mstore(0x40, fmp)
    }
  }

  function hash(
    ITokenizationSpoke.TokenizedDeposit calldata params
  ) internal pure returns (bytes32) {
    return
      keccak256(
        abi.encode(
          TOKENIZED_DEPOSIT_TYPEHASH,
          params.depositor,
          params.assets,
          params.receiver,
          params.nonce,
          params.deadline
        )
      );
  }

  function hash(ITokenizationSpoke.TokenizedMint calldata params) internal pure returns (bytes32) {
    return
      keccak256(
        abi.encode(
          TOKENIZED_MINT_TYPEHASH,
          params.depositor,
          params.shares,
          params.receiver,
          params.nonce,
          params.deadline
        )
      );
  }

  function hash(
    ITokenizationSpoke.TokenizedWithdraw calldata params
  ) internal pure returns (bytes32) {
    return
      keccak256(
        abi.encode(
          TOKENIZED_WITHDRAW_TYPEHASH,
          params.owner,
          params.assets,
          params.receiver,
          params.nonce,
          params.deadline
        )
      );
  }

  function hash(
    ITokenizationSpoke.TokenizedRedeem calldata params
  ) internal pure returns (bytes32) {
    return
      keccak256(
        abi.encode(
          TOKENIZED_REDEEM_TYPEHASH,
          params.owner,
          params.shares,
          params.receiver,
          params.nonce,
          params.deadline
        )
      );
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

// src/spoke/Spoke.sol

/// @title Spoke
/// @author Aave Labs
/// @notice Handles risk configuration & borrowing strategy for reserves and user positions.
/// @dev Each reserve can be associated with a separate Hub.
abstract contract Spoke is
  ISpoke,
  SpokeStorage,
  AccessManagedUpgradeable,
  IntentConsumer,
  ExtSload,
  Multicall,
  ReentrancyGuardTransient
{
  using SafeCast for *;
  using SafeERC20 for IERC20;
  using MathUtils for *;
  using PercentageMath for *;
  using WadRayMath for *;
  using SpokeUtils for *;
  using EIP712Hash for *;
  using KeyValueList for KeyValueList.List;
  using PositionStatusMap for *;
  using ReserveFlagsMap for ReserveFlags;
  using UserPositionUtils for ISpoke.UserPosition;

  /// @inheritdoc ISpoke
  bytes32 public constant SET_USER_POSITION_MANAGERS_TYPEHASH =
    EIP712Hash.SET_USER_POSITION_MANAGERS_TYPEHASH;

  /// @inheritdoc ISpoke
  uint16 public immutable MAX_USER_RESERVES_LIMIT;

  /// @inheritdoc ISpoke
  address public immutable ORACLE;

  /// @dev The number of decimals used by the oracle.
  uint8 internal constant ORACLE_DECIMALS = SpokeUtils.ORACLE_DECIMALS;

  /// @dev The maximum allowed value for an asset identifier (inclusive).
  uint256 internal constant MAX_ALLOWED_ASSET_ID = type(uint16).max;

  /// @dev The maximum allowed collateral risk value for a reserve, expressed in BPS (e.g. 100_00 is 100.00%).
  uint24 internal constant MAX_ALLOWED_COLLATERAL_RISK = 1000_00;

  /// @dev The maximum allowed value for a dynamic configuration key (inclusive).
  uint256 internal constant MAX_ALLOWED_DYNAMIC_CONFIG_KEY = type(uint32).max;

  /// @dev The maximum allowed value for the maximum number of reserves a user can have (collateral or borrowed) (inclusive).
  uint16 internal constant MAX_ALLOWED_USER_RESERVES_LIMIT = type(uint16).max;

  /// @dev The minimum health factor below which a position is considered unhealthy and subject to liquidation.
  /// @dev Expressed in WAD (18 decimals) (e.g. 1e18 is 1.00).
  uint64 internal constant HEALTH_FACTOR_LIQUIDATION_THRESHOLD =
    LiquidationLogic.HEALTH_FACTOR_LIQUIDATION_THRESHOLD;

  /// @dev The maximum amount considered as dust for a user's collateral and debt balances after a liquidation.
  /// @dev Worth 1000 USD, expressed in units of Value. 1e26 represents 1 USD.
  uint256 internal constant DUST_LIQUIDATION_THRESHOLD =
    LiquidationLogic.DUST_LIQUIDATION_THRESHOLD;

  /// @notice Modifier that checks if the caller is an approved positionManager for `onBehalfOf`.
  modifier onlyPositionManager(address onBehalfOf) {
    require(_isPositionManager({user: onBehalfOf, manager: msg.sender}), Unauthorized());
    _;
  }

  /// @dev Constructor.
  /// @param oracle_ The address of the AaveOracle contract.
  /// @param maxUserReservesLimit_ The maximum number of collateral and borrow reserves a user can have.
  constructor(address oracle_, uint16 maxUserReservesLimit_) {
    require(IAaveOracle(oracle_).decimals() == ORACLE_DECIMALS, InvalidOracleDecimals());
    require(maxUserReservesLimit_ > 0, InvalidMaxUserReservesLimit());
    ORACLE = oracle_;
    MAX_USER_RESERVES_LIMIT = maxUserReservesLimit_;
  }

  /// @dev To be overridden by the inheriting Spoke instance contract.
  function initialize(address authority) external virtual;

  /// @inheritdoc ISpoke
  function updateLiquidationConfig(LiquidationConfig calldata config) external restricted {
    require(
      config.targetHealthFactor >= HEALTH_FACTOR_LIQUIDATION_THRESHOLD &&
        config.liquidationBonusFactor <= PercentageMath.PERCENTAGE_FACTOR &&
        config.healthFactorForMaxBonus < HEALTH_FACTOR_LIQUIDATION_THRESHOLD,
      InvalidLiquidationConfig()
    );
    _liquidationConfig = config;
    emit UpdateLiquidationConfig(config);
  }

  /// @inheritdoc ISpoke
  function addReserve(
    address hub,
    uint256 assetId,
    address priceSource,
    ReserveConfig calldata config,
    DynamicReserveConfig calldata dynamicConfig
  ) external restricted returns (uint256) {
    require(hub != address(0), InvalidAddress());
    require(assetId <= MAX_ALLOWED_ASSET_ID, InvalidAssetId());
    require(!_isAssetIdListed(hub, assetId, _hubAssetIdToReserveId[hub][assetId]), ReserveExists());

    _validateReserveConfig(config);
    _validateDynamicReserveConfig(dynamicConfig);
    uint256 reserveId = _reserveCount++;
    _hubAssetIdToReserveId[hub][assetId] = reserveId;

    (address underlying, uint8 decimals) = IHubBase(hub).getAssetUnderlyingAndDecimals(assetId);
    require(underlying != address(0), AssetNotListed());
    require(decimals <= WadRayMath.WAD_DECIMALS, InvalidAssetDecimals());

    _updateReservePriceSource(reserveId, priceSource);

    uint32 dynamicConfigKey; // 0 as first key to use
    _reserves[reserveId] = Reserve({
      underlying: underlying,
      hub: IHubBase(hub),
      assetId: assetId.toUint16(),
      decimals: decimals,
      collateralRisk: config.collateralRisk,
      flags: ReserveFlagsMap.create({
        initPaused: config.paused,
        initFrozen: config.frozen,
        initBorrowable: config.borrowable,
        initReceiveSharesEnabled: config.receiveSharesEnabled
      }),
      dynamicConfigKey: dynamicConfigKey
    });
    _dynamicConfig[reserveId][dynamicConfigKey] = dynamicConfig;

    emit AddReserve(reserveId, assetId, hub);
    emit UpdateReserveConfig(reserveId, config);
    emit AddDynamicReserveConfig(reserveId, dynamicConfigKey, dynamicConfig);

    return reserveId;
  }

  /// @inheritdoc ISpoke
  function updateReserveConfig(
    uint256 reserveId,
    ReserveConfig calldata config
  ) external restricted {
    Reserve storage reserve = _reserves.get(reserveId);
    _validateReserveConfig(config);
    reserve.collateralRisk = config.collateralRisk;
    reserve.flags = ReserveFlagsMap.create({
      initPaused: config.paused,
      initFrozen: config.frozen,
      initBorrowable: config.borrowable,
      initReceiveSharesEnabled: config.receiveSharesEnabled
    });
    emit UpdateReserveConfig(reserveId, config);
  }

  /// @inheritdoc ISpoke
  function updateReservePriceSource(uint256 reserveId, address priceSource) external restricted {
    require(reserveId < _reserveCount, ReserveNotListed());
    _updateReservePriceSource(reserveId, priceSource);
  }

  /// @inheritdoc ISpoke
  function addDynamicReserveConfig(
    uint256 reserveId,
    DynamicReserveConfig calldata dynamicConfig
  ) external restricted returns (uint32) {
    require(reserveId < _reserveCount, ReserveNotListed());
    uint32 dynamicConfigKey = _reserves[reserveId].dynamicConfigKey;
    require(dynamicConfigKey < MAX_ALLOWED_DYNAMIC_CONFIG_KEY, MaximumDynamicConfigKeyReached());
    _validateDynamicReserveConfig(dynamicConfig);
    dynamicConfigKey = dynamicConfigKey.uncheckedAdd(1).toUint32();
    _reserves[reserveId].dynamicConfigKey = dynamicConfigKey;
    _dynamicConfig[reserveId][dynamicConfigKey] = dynamicConfig;
    emit AddDynamicReserveConfig(reserveId, dynamicConfigKey, dynamicConfig);
    return dynamicConfigKey;
  }

  /// @inheritdoc ISpoke
  function updateDynamicReserveConfig(
    uint256 reserveId,
    uint32 dynamicConfigKey,
    DynamicReserveConfig calldata dynamicConfig
  ) external restricted {
    require(reserveId < _reserveCount, ReserveNotListed());
    _validateUpdateDynamicReserveConfig(_dynamicConfig[reserveId][dynamicConfigKey], dynamicConfig);
    _dynamicConfig[reserveId][dynamicConfigKey] = dynamicConfig;
    emit UpdateDynamicReserveConfig(reserveId, dynamicConfigKey, dynamicConfig);
  }

  /// @inheritdoc ISpoke
  function updatePositionManager(address positionManager, bool active) external restricted {
    _positionManager[positionManager].active = active;
    emit UpdatePositionManager(positionManager, active);
  }

  /// @inheritdoc ISpoke
  function supply(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external nonReentrant onlyPositionManager(onBehalfOf) returns (uint256, uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    UserPosition storage userPosition = _userPositions[onBehalfOf][reserveId];
    _validateSupply(reserve.flags);

    IERC20(reserve.underlying).safeTransferFrom(msg.sender, address(reserve.hub), amount);
    uint256 suppliedShares = reserve.hub.add(reserve.assetId, amount);
    userPosition.suppliedShares += suppliedShares.toUint120();

    emit Supply(reserveId, msg.sender, onBehalfOf, suppliedShares, amount);

    return (suppliedShares, amount);
  }

  /// @inheritdoc ISpoke
  function withdraw(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external nonReentrant onlyPositionManager(onBehalfOf) returns (uint256, uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    UserPosition storage userPosition = _userPositions[onBehalfOf][reserveId];
    _validateWithdraw(reserve.flags);
    IHubBase hub = reserve.hub;
    uint256 assetId = reserve.assetId;

    uint256 withdrawnAmount = MathUtils.min(
      amount,
      hub.previewRemoveByShares(assetId, userPosition.suppliedShares)
    );
    uint256 withdrawnShares = hub.remove(assetId, withdrawnAmount, msg.sender);

    userPosition.suppliedShares -= withdrawnShares.toUint120();

    if (_positionStatus[onBehalfOf].isUsingAsCollateral(reserveId)) {
      uint256 newRiskPremium = _refreshAndValidateUserAccountData(onBehalfOf).riskPremium;
      _notifyRiskPremiumUpdate(onBehalfOf, newRiskPremium);
    }

    emit Withdraw(reserveId, msg.sender, onBehalfOf, withdrawnShares, withdrawnAmount);

    return (withdrawnShares, withdrawnAmount);
  }

  /// @inheritdoc ISpoke
  function borrow(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external nonReentrant onlyPositionManager(onBehalfOf) returns (uint256, uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    UserPosition storage userPosition = _userPositions[onBehalfOf][reserveId];
    PositionStatus storage positionStatus = _positionStatus[onBehalfOf];
    _validateBorrow(reserve.flags);
    IHubBase hub = reserve.hub;

    uint256 drawnShares = hub.draw(reserve.assetId, amount, msg.sender);
    userPosition.drawnShares += drawnShares.toUint120();
    if (!positionStatus.isBorrowing(reserveId)) {
      require(
        MAX_USER_RESERVES_LIMIT == MAX_ALLOWED_USER_RESERVES_LIMIT ||
          positionStatus.borrowCount(_reserveCount) < MAX_USER_RESERVES_LIMIT,
        MaximumUserReservesExceeded()
      );
      positionStatus.setBorrowing(reserveId, true);
    }

    uint256 newRiskPremium = _refreshAndValidateUserAccountData(onBehalfOf).riskPremium;
    _notifyRiskPremiumUpdate(onBehalfOf, newRiskPremium);

    emit Borrow(reserveId, msg.sender, onBehalfOf, drawnShares, amount);

    return (drawnShares, amount);
  }

  /// @inheritdoc ISpoke
  function repay(
    uint256 reserveId,
    uint256 amount,
    address onBehalfOf
  ) external nonReentrant onlyPositionManager(onBehalfOf) returns (uint256, uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    UserPosition storage userPosition = _userPositions[onBehalfOf][reserveId];
    _validateRepay(reserve.flags);

    uint256 drawnIndex = reserve.hub.getAssetDrawnIndex(reserve.assetId);
    (uint256 drawnDebtRestored, uint256 premiumDebtRayRestored) = userPosition
      .calculateRestoreAmount(drawnIndex, amount);
    uint256 restoredShares = drawnDebtRestored.rayDivDown(drawnIndex);

    IHubBase.PremiumDelta memory premiumDelta = userPosition.calculatePremiumDelta({
      drawnSharesTaken: restoredShares,
      drawnIndex: drawnIndex,
      riskPremium: _positionStatus[onBehalfOf].riskPremium,
      restoredPremiumRay: premiumDebtRayRestored
    });

    uint256 totalDebtRestored = drawnDebtRestored + premiumDebtRayRestored.fromRayUp();
    IERC20(reserve.underlying).safeTransferFrom(
      msg.sender,
      address(reserve.hub),
      totalDebtRestored
    );
    reserve.hub.restore(reserve.assetId, drawnDebtRestored, premiumDelta);

    userPosition.applyPremiumDelta(premiumDelta);
    userPosition.drawnShares -= restoredShares.toUint120();
    if (userPosition.drawnShares == 0) {
      PositionStatus storage positionStatus = _positionStatus[onBehalfOf];
      positionStatus.setBorrowing(reserveId, false);
    }

    emit Repay(reserveId, msg.sender, onBehalfOf, restoredShares, totalDebtRestored, premiumDelta);

    return (restoredShares, totalDebtRestored);
  }

  /// @inheritdoc ISpoke
  function liquidationCall(
    uint256 collateralReserveId,
    uint256 debtReserveId,
    address user,
    uint256 debtToCover,
    bool receiveShares
  ) external nonReentrant {
    UserAccountData memory userAccountData = _calculateUserAccountData(user);
    LiquidationLogic.LiquidateUserParams memory params = LiquidationLogic.LiquidateUserParams({
      collateralReserveId: collateralReserveId,
      debtReserveId: debtReserveId,
      liquidationConfig: _liquidationConfig,
      oracle: ORACLE,
      user: user,
      debtToCover: debtToCover,
      userAccountData: userAccountData,
      liquidator: msg.sender,
      receiveShares: receiveShares
    });

    bool isUserInDeficit = LiquidationLogic.liquidateUser({
      reserves: _reserves,
      userPositions: _userPositions,
      positionStatus: _positionStatus,
      dynamicConfig: _dynamicConfig,
      params: params
    });

    if (isUserInDeficit) {
      // report deficit for all debt reserves, including the reserve being repaid
      LiquidationLogic.notifyReportDeficit(
        _reserves,
        _userPositions,
        _positionStatus,
        _reserveCount,
        user
      );
    } else {
      uint256 newRiskPremium = _calculateUserAccountData(user).riskPremium;
      _notifyRiskPremiumUpdate(user, newRiskPremium);
    }
  }

  /// @inheritdoc ISpoke
  function setUsingAsCollateral(
    uint256 reserveId,
    bool usingAsCollateral,
    address onBehalfOf
  ) external nonReentrant onlyPositionManager(onBehalfOf) {
    Reserve storage reserve = _reserves.get(reserveId);
    PositionStatus storage positionStatus = _positionStatus[onBehalfOf];
    if (positionStatus.isUsingAsCollateral(reserveId) == usingAsCollateral) {
      return;
    }
    _validateSetUsingAsCollateral(positionStatus, reserve.flags, usingAsCollateral);
    positionStatus.setUsingAsCollateral(reserveId, usingAsCollateral);

    if (usingAsCollateral) {
      _refreshDynamicConfig(onBehalfOf, reserveId);
    } else {
      uint256 newRiskPremium = _refreshAndValidateUserAccountData(onBehalfOf).riskPremium;
      _notifyRiskPremiumUpdate(onBehalfOf, newRiskPremium);
    }

    emit SetUsingAsCollateral(reserveId, msg.sender, onBehalfOf, usingAsCollateral);
  }

  /// @inheritdoc ISpoke
  function updateUserRiskPremium(address onBehalfOf) external nonReentrant {
    if (!_isPositionManager({user: onBehalfOf, manager: msg.sender})) {
      _checkCanCall(msg.sender, msg.data);
    }
    uint256 newRiskPremium = _calculateUserAccountData(onBehalfOf).riskPremium;
    _notifyRiskPremiumUpdate(onBehalfOf, newRiskPremium);
  }

  /// @inheritdoc ISpoke
  function updateUserDynamicConfig(address onBehalfOf) external nonReentrant {
    if (!_isPositionManager({user: onBehalfOf, manager: msg.sender})) {
      _checkCanCall(msg.sender, msg.data);
    }
    uint256 newRiskPremium = _refreshAndValidateUserAccountData(onBehalfOf).riskPremium;
    _notifyRiskPremiumUpdate(onBehalfOf, newRiskPremium);
  }

  /// @inheritdoc ISpoke
  function setUserPositionManager(address positionManager, bool approve) external {
    _setUserPositionManager({positionManager: positionManager, user: msg.sender, approve: approve});
  }

  /// @inheritdoc ISpoke
  function setUserPositionManagersWithSig(
    SetUserPositionManagers calldata params,
    bytes calldata signature
  ) external {
    _verifyAndConsumeIntent({
      signer: params.onBehalfOf,
      intentHash: params.hash(),
      nonce: params.nonce,
      deadline: params.deadline,
      signature: signature
    });

    for (uint256 i = 0; i < params.updates.length; ++i) {
      _setUserPositionManager({
        positionManager: params.updates[i].positionManager,
        user: params.onBehalfOf,
        approve: params.updates[i].approve
      });
    }
  }

  /// @inheritdoc ISpoke
  function renouncePositionManagerRole(address onBehalfOf) external {
    if (!_positionManager[msg.sender].approval[onBehalfOf]) {
      return;
    }
    _positionManager[msg.sender].approval[onBehalfOf] = false;
    emit SetUserPositionManager(onBehalfOf, msg.sender, false);
  }

  /// @inheritdoc ISpoke
  function permitReserve(
    uint256 reserveId,
    address onBehalfOf,
    uint256 value,
    uint256 deadline,
    uint8 permitV,
    bytes32 permitR,
    bytes32 permitS
  ) external {
    Reserve storage reserve = _reserves[reserveId];
    address underlying = reserve.underlying;
    require(underlying != address(0), ReserveNotListed());
    try
      IERC20Permit(underlying).permit({
        owner: onBehalfOf,
        spender: address(this),
        value: value,
        deadline: deadline,
        v: permitV,
        r: permitR,
        s: permitS
      })
    {} catch {}
  }

  /// @inheritdoc ISpoke
  function getLiquidationConfig() external view returns (LiquidationConfig memory) {
    return _liquidationConfig;
  }

  /// @inheritdoc ISpoke
  function getReserveCount() external view returns (uint256) {
    return _reserveCount;
  }

  /// @inheritdoc ISpoke
  function getReserveSuppliedAssets(uint256 reserveId) external view returns (uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    return reserve.hub.getSpokeAddedAssets(reserve.assetId, address(this));
  }

  /// @inheritdoc ISpoke
  function getReserveSuppliedShares(uint256 reserveId) external view returns (uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    return reserve.hub.getSpokeAddedShares(reserve.assetId, address(this));
  }

  /// @inheritdoc ISpoke
  function getReserveDebt(uint256 reserveId) external view returns (uint256, uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    return reserve.hub.getSpokeOwed(reserve.assetId, address(this));
  }

  /// @inheritdoc ISpoke
  function getReserveTotalDebt(uint256 reserveId) external view returns (uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    return reserve.hub.getSpokeTotalOwed(reserve.assetId, address(this));
  }

  /// @inheritdoc ISpoke
  function getReserveId(address hub, uint256 assetId) external view returns (uint256) {
    uint256 reserveId = _hubAssetIdToReserveId[hub][assetId];
    require(_isAssetIdListed(hub, assetId, reserveId), ReserveNotListed());
    return reserveId;
  }

  /// @inheritdoc ISpoke
  function getReserve(uint256 reserveId) external view returns (Reserve memory) {
    return _reserves.get(reserveId);
  }

  /// @inheritdoc ISpoke
  function getReserveConfig(uint256 reserveId) external view returns (ReserveConfig memory) {
    Reserve storage reserve = _reserves.get(reserveId);
    return
      ReserveConfig({
        collateralRisk: reserve.collateralRisk,
        paused: reserve.flags.paused(),
        frozen: reserve.flags.frozen(),
        borrowable: reserve.flags.borrowable(),
        receiveSharesEnabled: reserve.flags.receiveSharesEnabled()
      });
  }

  /// @inheritdoc ISpoke
  function getDynamicReserveConfig(
    uint256 reserveId,
    uint32 dynamicConfigKey
  ) external view returns (DynamicReserveConfig memory) {
    _reserves.get(reserveId);
    return _dynamicConfig[reserveId][dynamicConfigKey];
  }

  /// @inheritdoc ISpoke
  function getUserReserveStatus(
    uint256 reserveId,
    address user
  ) external view returns (bool, bool) {
    _reserves.get(reserveId);
    PositionStatus storage positionStatus = _positionStatus[user];
    return (positionStatus.isUsingAsCollateral(reserveId), positionStatus.isBorrowing(reserveId));
  }

  /// @inheritdoc ISpoke
  function getUserSuppliedAssets(uint256 reserveId, address user) external view returns (uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    return
      reserve.hub.previewRemoveByShares(
        reserve.assetId,
        _userPositions[user][reserveId].suppliedShares
      );
  }

  /// @inheritdoc ISpoke
  function getUserSuppliedShares(uint256 reserveId, address user) external view returns (uint256) {
    _reserves.get(reserveId);
    return _userPositions[user][reserveId].suppliedShares;
  }

  /// @inheritdoc ISpoke
  function getUserDebt(uint256 reserveId, address user) external view returns (uint256, uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    UserPosition storage userPosition = _userPositions[user][reserveId];
    (uint256 drawnDebt, uint256 premiumDebtRay) = userPosition.getDebt(
      reserve.hub,
      reserve.assetId
    );
    return (drawnDebt, premiumDebtRay.fromRayUp());
  }

  /// @inheritdoc ISpoke
  function getUserTotalDebt(uint256 reserveId, address user) external view returns (uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    UserPosition storage userPosition = _userPositions[user][reserveId];
    (uint256 drawnDebt, uint256 premiumDebtRay) = userPosition.getDebt(
      reserve.hub,
      reserve.assetId
    );
    return (drawnDebt + premiumDebtRay.fromRayUp());
  }

  /// @inheritdoc ISpoke
  function getUserPremiumDebtRay(uint256 reserveId, address user) external view returns (uint256) {
    Reserve storage reserve = _reserves.get(reserveId);
    UserPosition storage userPosition = _userPositions[user][reserveId];
    (, uint256 premiumDebtRay) = userPosition.getDebt(reserve.hub, reserve.assetId);
    return premiumDebtRay;
  }

  /// @inheritdoc ISpoke
  function getUserPosition(
    uint256 reserveId,
    address user
  ) external view returns (UserPosition memory) {
    _reserves.get(reserveId);
    return _userPositions[user][reserveId];
  }

  /// @inheritdoc ISpoke
  function getUserLastRiskPremium(address user) external view returns (uint256) {
    return _positionStatus[user].riskPremium;
  }

  /// @inheritdoc ISpoke
  function getUserAccountData(address user) external view returns (UserAccountData memory) {
    // SAFETY: function does not modify state when `refreshConfig` is false.
    return _castToView(_processUserAccountData)(user, false);
  }

  /// @inheritdoc ISpoke
  function getLiquidationBonus(
    uint256 reserveId,
    address user,
    uint256 healthFactor
  ) external view returns (uint256) {
    _reserves.get(reserveId);
    return
      LiquidationLogic.calculateLiquidationBonus({
        healthFactorForMaxBonus: _liquidationConfig.healthFactorForMaxBonus,
        liquidationBonusFactor: _liquidationConfig.liquidationBonusFactor,
        healthFactor: healthFactor,
        maxLiquidationBonus: _dynamicConfig[reserveId][
          _userPositions[user][reserveId].dynamicConfigKey
        ].maxLiquidationBonus
      });
  }

  /// @inheritdoc ISpoke
  function isPositionManagerActive(address positionManager) external view returns (bool) {
    return _positionManager[positionManager].active;
  }

  /// @inheritdoc ISpoke
  function isPositionManager(address user, address positionManager) external view returns (bool) {
    return _isPositionManager(user, positionManager);
  }

  /// @inheritdoc ISpoke
  function getLiquidationLogic() external pure returns (address) {
    return address(LiquidationLogic);
  }

  function _updateReservePriceSource(uint256 reserveId, address priceSource) internal {
    require(priceSource != address(0), InvalidAddress());
    IAaveOracle(ORACLE).setReserveSource(reserveId, priceSource);
    emit UpdateReservePriceSource(reserveId, priceSource);
  }

  function _setUserPositionManager(address positionManager, address user, bool approve) internal {
    PositionManagerConfig storage config = _positionManager[positionManager];
    config.approval[user] = approve;
    emit SetUserPositionManager(user, positionManager, approve);
  }

  /// @notice Calculates and validates the user account data.
  /// @dev It refreshes the dynamic config before calculation.
  /// @dev It checks that the health factor is above the liquidation threshold.
  function _refreshAndValidateUserAccountData(
    address user
  ) internal returns (UserAccountData memory) {
    UserAccountData memory accountData = _processUserAccountData(user, true);
    emit RefreshAllUserDynamicConfig(user);
    require(
      accountData.healthFactor >= HEALTH_FACTOR_LIQUIDATION_THRESHOLD,
      HealthFactorBelowThreshold()
    );
    return accountData;
  }

  /// @notice Calculates the user account data with the current user dynamic config.
  function _calculateUserAccountData(address user) internal returns (UserAccountData memory) {
    return _processUserAccountData(user, false); // does not modify state
  }

  /// @notice Process the user account data and updates dynamic config of the user if `refreshConfig` is true.
  /// @dev Collateral is rounded against the user, while debt is calculated with full precision.
  /// @dev If user has no debt, it returns health factor of `type(uint256).max` and risk premium of 0.
  function _processUserAccountData(
    address user,
    bool refreshConfig
  ) internal returns (UserAccountData memory accountData) {
    PositionStatus storage positionStatus = _positionStatus[user];

    uint256 reserveId = _reserveCount;
    KeyValueList.List memory collateralInfo = KeyValueList.init(
      positionStatus.collateralCount(reserveId)
    );
    bool borrowing;
    bool collateral;
    while (true) {
      (reserveId, borrowing, collateral) = positionStatus.next(reserveId);
      if (reserveId == PositionStatusMap.NOT_FOUND) break;

      UserPosition storage userPosition = _userPositions[user][reserveId];
      Reserve storage reserve = _reserves[reserveId];

      uint256 assetPrice = IAaveOracle(ORACLE).getReservePrice(reserveId);
      uint256 assetDecimals = reserve.decimals;

      if (collateral) {
        uint256 collateralFactor = _dynamicConfig[reserveId][
          refreshConfig
            ? (userPosition.dynamicConfigKey = reserve.dynamicConfigKey)
            : userPosition.dynamicConfigKey
        ].collateralFactor;
        if (collateralFactor > 0) {
          uint256 suppliedShares = userPosition.suppliedShares;
          if (suppliedShares > 0) {
            // cannot round down to zero
            uint256 userCollateralValue = reserve
              .hub
              .previewRemoveByShares(reserve.assetId, suppliedShares)
              .toValue({decimals: assetDecimals, price: assetPrice});
            accountData.totalCollateralValue += userCollateralValue;
            collateralInfo.add(
              accountData.activeCollateralCount,
              reserve.collateralRisk,
              userCollateralValue
            );
            accountData.avgCollateralFactor += collateralFactor * userCollateralValue;
            accountData.activeCollateralCount = accountData.activeCollateralCount.uncheckedAdd(1);
          }
        }
      }

      if (borrowing) {
        UserPositionUtils.DebtComponents memory debtComponents = userPosition.getDebtComponents(
          reserve.hub,
          reserve.assetId
        );
        uint256 debtRay = debtComponents.drawnShares * debtComponents.drawnIndex +
          debtComponents.premiumDebtRay;
        accountData.totalDebtValueRay += debtRay.toValue({
          decimals: assetDecimals,
          price: assetPrice
        });
        accountData.borrowCount = accountData.borrowCount.uncheckedAdd(1);
      }
    }

    if (accountData.totalDebtValueRay > 0) {
      // at this point, `avgCollateralFactor` is the total collateral value weighted by collateral factors,
      // expressed in units of Value and scaled by BPS. We convert it from BPS to WAD, since this will
      // ultimately define the scaling factor of the health factor.
      accountData.healthFactor = Math.mulDiv(
        accountData.avgCollateralFactor.bpsToWad(),
        WadRayMath.RAY,
        accountData.totalDebtValueRay,
        Math.Rounding.Floor
      );
    } else {
      accountData.healthFactor = type(uint256).max;
    }

    if (accountData.totalCollateralValue > 0) {
      accountData.avgCollateralFactor =
        accountData.avgCollateralFactor.bpsToWad() / accountData.totalCollateralValue;
    }

    // sort by collateral risk in ASC, collateral value in DESC
    collateralInfo.sortByKey();

    // runs until either the collateral or debt is exhausted
    uint256 totalDebtValue = accountData.totalDebtValueRay.fromRayUp();
    uint256 debtValueLeftToCover = totalDebtValue;

    for (uint256 index = 0; index < collateralInfo.length(); ++index) {
      if (debtValueLeftToCover == 0) {
        break;
      }

      (uint256 collateralRisk, uint256 userCollateralValue) = collateralInfo.uncheckedAt(index);
      userCollateralValue = userCollateralValue.min(debtValueLeftToCover);
      accountData.riskPremium += userCollateralValue * collateralRisk;
      debtValueLeftToCover = debtValueLeftToCover.uncheckedSub(userCollateralValue);
    }

    if (debtValueLeftToCover < totalDebtValue) {
      accountData.riskPremium = accountData.riskPremium.divUp(
        totalDebtValue.uncheckedSub(debtValueLeftToCover)
      );
    }

    return accountData;
  }

  function _refreshDynamicConfig(address user, uint256 reserveId) internal {
    _userPositions[user][reserveId].dynamicConfigKey = _reserves[reserveId].dynamicConfigKey;
    emit RefreshSingleUserDynamicConfig(user, reserveId);
  }

  /// @notice Refreshes premium for borrowed reserves of `user` with `newRiskPremium`.
  /// @dev Skips the refresh if the user risk premium remains zero.
  function _notifyRiskPremiumUpdate(address user, uint256 newRiskPremium) internal {
    PositionStatus storage positionStatus = _positionStatus[user];
    if (newRiskPremium == 0 && positionStatus.riskPremium == 0) {
      return;
    }
    positionStatus.riskPremium = newRiskPremium.toUint24();

    uint256 reserveId = _reserveCount;
    while ((reserveId = positionStatus.nextBorrowing(reserveId)) != PositionStatusMap.NOT_FOUND) {
      UserPosition storage userPosition = _userPositions[user][reserveId];
      Reserve storage reserve = _reserves[reserveId];
      uint256 assetId = reserve.assetId;
      IHubBase hub = reserve.hub;

      IHubBase.PremiumDelta memory premiumDelta = userPosition.calculatePremiumDelta({
        drawnSharesTaken: 0,
        drawnIndex: hub.getAssetDrawnIndex(assetId),
        riskPremium: newRiskPremium,
        restoredPremiumRay: 0
      });

      hub.refreshPremium(assetId, premiumDelta);
      userPosition.applyPremiumDelta(premiumDelta);
      emit RefreshPremiumDebt(reserveId, user, premiumDelta);
    }

    emit UpdateUserRiskPremium(user, newRiskPremium);
  }

  /// @dev CollateralFactor of historical config keys cannot be 0, which allows liquidations to proceed.
  function _validateUpdateDynamicReserveConfig(
    DynamicReserveConfig storage currentConfig,
    DynamicReserveConfig calldata newConfig
  ) internal view {
    // sufficient check since maxLiquidationBonus is always >= 100_00
    require(currentConfig.maxLiquidationBonus > 0, DynamicConfigKeyUninitialized());
    require(newConfig.collateralFactor > 0, InvalidCollateralFactor());
    _validateDynamicReserveConfig(newConfig);
  }

  function _validateSupply(ReserveFlags flags) internal pure {
    require(!flags.paused(), ReservePaused());
    require(!flags.frozen(), ReserveFrozen());
  }

  function _validateWithdraw(ReserveFlags flags) internal pure {
    require(!flags.paused(), ReservePaused());
  }

  function _validateBorrow(ReserveFlags flags) internal pure {
    require(!flags.paused(), ReservePaused());
    require(!flags.frozen(), ReserveFrozen());
    require(flags.borrowable(), ReserveNotBorrowable());
    // health factor is checked at the end of borrow action
  }

  function _validateRepay(ReserveFlags flags) internal pure {
    require(!flags.paused(), ReservePaused());
  }

  function _validateSetUsingAsCollateral(
    PositionStatus storage positionStatus,
    ReserveFlags flags,
    bool usingAsCollateral
  ) internal view {
    require(!flags.paused(), ReservePaused());
    if (usingAsCollateral) {
      // disabling as collateral is allowed when reserve is frozen
      require(!flags.frozen(), ReserveFrozen());
      // this must be a new collateral, otherwise would have short-circuited
      require(
        MAX_USER_RESERVES_LIMIT == MAX_ALLOWED_USER_RESERVES_LIMIT ||
          positionStatus.collateralCount(_reserveCount) < MAX_USER_RESERVES_LIMIT,
        MaximumUserReservesExceeded()
      );
    }
  }

  function _isAssetIdListed(
    address hub,
    uint256 assetId,
    uint256 reserveId
  ) internal view returns (bool) {
    return _reserves[reserveId].assetId == assetId && address(_reserves[reserveId].hub) == hub;
  }

  /// @notice Returns whether `manager` is active and approved positionManager for `user`.
  function _isPositionManager(address user, address manager) internal view returns (bool) {
    if (user == manager) return true;
    PositionManagerConfig storage config = _positionManager[manager];
    return config.active && config.approval[user];
  }

  function _validateReserveConfig(ReserveConfig calldata config) internal pure {
    require(config.collateralRisk <= MAX_ALLOWED_COLLATERAL_RISK, InvalidCollateralRisk());
  }

  /// @dev Enforces compatible `maxLiquidationBonus` and `collateralFactor` so at the moment debt is created
  /// there is enough collateral to cover liquidation.
  function _validateDynamicReserveConfig(DynamicReserveConfig calldata config) internal pure {
    require(
      config.collateralFactor < PercentageMath.PERCENTAGE_FACTOR &&
        config.maxLiquidationBonus >= PercentageMath.PERCENTAGE_FACTOR &&
        config.maxLiquidationBonus.percentMulUp(config.collateralFactor) <
          PercentageMath.PERCENTAGE_FACTOR,
      InvalidCollateralFactorAndMaxLiquidationBonus()
    );
    require(config.liquidationFee <= PercentageMath.PERCENTAGE_FACTOR, InvalidLiquidationFee());
  }

  function _domainNameAndVersion() internal pure override returns (string memory, string memory) {
    return ('Spoke', '1');
  }

  function _castToView(
    function(address, bool) internal returns (UserAccountData memory) fnIn
  )
    internal
    pure
    returns (function(address, bool) internal view returns (UserAccountData memory) fnOut)
  {
    assembly ('memory-safe') {
      fnOut := fnIn
    }
  }
}

// bench/SpokeBorrowRepay.sol

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

contract TestSpoke is Spoke {
  constructor(address oracle_, address authority_)
    Spoke(oracle_, type(uint16).max)
    initializer
  {
    __AccessManaged_init(authority_);
    _liquidationConfig.targetHealthFactor = HEALTH_FACTOR_LIQUIDATION_THRESHOLD;
  }

  function initialize(address) external pure override {}
}

contract SpokeActor {
  TestSpoke private immutable spoke;
  TestnetERC20 private immutable collateral;
  uint256 private immutable collateralReserveId;
  uint256 private immutable debtReserveId;

  constructor(
    TestSpoke spoke_,
    TestnetERC20 collateral_,
    uint256 collateralReserveId_,
    uint256 debtReserveId_
  ) {
    spoke = spoke_;
    collateral = collateral_;
    collateralReserveId = collateralReserveId_;
    debtReserveId = debtReserveId_;
    collateral_.approve(address(spoke_), type(uint256).max);
  }

  function supplyCollateral(uint256 amount) external {
    spoke.supply(collateralReserveId, amount, address(this));
    spoke.setUsingAsCollateral(collateralReserveId, true, address(this));
  }

  function borrow(uint256 amount) external {
    spoke.borrow(debtReserveId, amount, address(this));
  }
}

contract AGasTest {
  TestHub public immutable hub;
  TestSpoke public immutable spoke;
  TestnetERC20 public immutable usdx;
  TestnetERC20 public immutable dai;
  MockPriceFeed public immutable usdxPriceFeed;

  uint256 public immutable usdxReserveId;
  uint256 public immutable daiReserveId;

  SpokeActor private immutable liquidationPartialActor;
  SpokeActor private immutable liquidationFullActor;
  SpokeActor private immutable liquidationSharesPartialActor;
  SpokeActor private immutable liquidationSharesFullActor;
  SpokeActor private immutable liquidationDeficitActor;

  constructor() {
    AlwaysAllowAuthority authority = new AlwaysAllowAuthority();
    hub = new TestHub(address(authority));
    AssetInterestRateStrategy strategy = new AssetInterestRateStrategy(address(hub));
    usdx = new TestnetERC20('USDX', 'USDX', 6);
    dai = new TestnetERC20('DAI', 'DAI', 18);

    IAssetInterestRateStrategy.InterestRateData memory rateData =
      IAssetInterestRateStrategy.InterestRateData({
        optimalUsageRatio: 90_00,
        baseDrawnRate: 5_00,
        rateGrowthBeforeOptimal: 5_00,
        rateGrowthAfterOptimal: 5_00
      });
    uint256 usdxAssetId = hub.addAsset(
      address(usdx), 6, address(this), address(strategy), abi.encode(rateData)
    );
    uint256 daiAssetId = hub.addAsset(
      address(dai), 18, address(this), address(strategy), abi.encode(rateData)
    );

    AaveOracle oracle = new AaveOracle(8);
    spoke = new TestSpoke(address(oracle), address(authority));
    oracle.setSpoke(address(spoke));

    IHub.SpokeConfig memory spokeConfig = IHub.SpokeConfig({
      addCap: type(uint40).max,
      drawCap: type(uint40).max,
      riskPremiumThreshold: type(uint24).max,
      active: true,
      halted: false
    });
    hub.addSpoke(usdxAssetId, address(spoke), spokeConfig);
    hub.addSpoke(daiAssetId, address(spoke), spokeConfig);

    spoke.updateLiquidationConfig(ISpoke.LiquidationConfig({
      targetHealthFactor: 1.05e18,
      healthFactorForMaxBonus: 0.7e18,
      liquidationBonusFactor: 20_00
    }));
    ISpoke.ReserveConfig memory reserveConfig = ISpoke.ReserveConfig({
      collateralRisk: 20_00,
      paused: false,
      frozen: false,
      borrowable: true,
      receiveSharesEnabled: true
    });
    usdxPriceFeed = new MockPriceFeed(8, 'USDX / USD', 1e8);
    usdxReserveId = spoke.addReserve(
      address(hub),
      usdxAssetId,
      address(usdxPriceFeed),
      reserveConfig,
      ISpoke.DynamicReserveConfig({
        collateralFactor: 78_00,
        maxLiquidationBonus: 105_00,
        liquidationFee: 10_00
      })
    );
    daiReserveId = spoke.addReserve(
      address(hub),
      daiAssetId,
      address(new MockPriceFeed(8, 'DAI / USD', 1e8)),
      reserveConfig,
      ISpoke.DynamicReserveConfig({
        collateralFactor: 78_00,
        maxLiquidationBonus: 102_00,
        liquidationFee: 10_00
      })
    );

    usdx.mint(address(this), 2_000_000e6);
    dai.mint(address(this), 10_000_000e18);
    usdx.approve(address(spoke), type(uint256).max);
    dai.approve(address(spoke), type(uint256).max);

    // Matches Spoke.Operations' seeded DAI liquidity. The public scenario
    // sequence below performs the user's setup and actions in upstream order.
    spoke.supply(daiReserveId, 5_000_000e18, address(this));

    // Five isolated users reproduce the upstream liquidation gas scenarios.
    // Each borrows to HF 1.05 before the shared collateral price falls to 85%.
    liquidationPartialActor = _newLiquidationActor();
    liquidationFullActor = _newLiquidationActor();
    liquidationSharesPartialActor = _newLiquidationActor();
    liquidationSharesFullActor = _newLiquidationActor();
    liquidationDeficitActor = _newLiquidationActor();
    usdxPriceFeed.setPrice(85e6);
  }

  function _newLiquidationActor() internal returns (SpokeActor actor) {
    actor = new SpokeActor(spoke, usdx, usdxReserveId, daiReserveId);
    usdx.mint(address(actor), 1_000_000e6);
    actor.supplyCollateral(1_000_000e6);

    // This is the calculation used by Aave's
    // _borrowToBeLiquidatableWithPriceChange helper for desired HF 1.05.
    ISpoke.UserAccountData memory data = spoke.getUserAccountData(address(actor));
    uint256 adjustedCollateral = data.totalCollateralValue * data.avgCollateralFactor / 1e18;
    uint256 targetDebtValue = (adjustedCollateral * 1e18 + 1.05e18 - 1) / 1.05e18;
    actor.borrow(targetDebtValue / 1e8);
  }

  function supplyFirst() external {
    spoke.supply(usdxReserveId, 1000e6, address(this));
  }

  function supplySecondSameReserve() external {
    spoke.supply(usdxReserveId, 1000e6, address(this));
  }

  function enableCollateral() external {
    spoke.setUsingAsCollateral(usdxReserveId, true, address(this));
  }

  function borrowFirst() external {
    spoke.borrow(daiReserveId, 500e18, address(this));
  }

  function borrowSecondSameReserve() external {
    spoke.borrow(daiReserveId, 1e18, address(this));
  }

  function getUserAccountData()
    external
    view
    returns (ISpoke.UserAccountData memory)
  {
    return spoke.getUserAccountData(address(this));
  }

  function updateUserRiskPremium() external {
    spoke.updateUserRiskPremium(address(this));
  }

  function updateUserDynamicConfig() external {
    spoke.updateUserDynamicConfig(address(this));
  }

  function repayPartial() external {
    spoke.repay(daiReserveId, 200e18, address(this));
  }

  function repayFull() external {
    spoke.repay(daiReserveId, type(uint256).max, address(this));
  }

  function withdrawPartial() external {
    spoke.withdraw(usdxReserveId, 1e6, address(this));
  }

  function withdrawFull() external {
    spoke.withdraw(usdxReserveId, type(uint256).max, address(this));
  }

  function liquidationPartial() external {
    spoke.liquidationCall(
      usdxReserveId,
      daiReserveId,
      address(liquidationPartialActor),
      100_000e18,
      false
    );
  }

  function liquidationFull() external {
    spoke.liquidationCall(
      usdxReserveId,
      daiReserveId,
      address(liquidationFullActor),
      type(uint256).max,
      false
    );
  }

  function liquidationReceiveSharesPartial() external {
    spoke.liquidationCall(
      usdxReserveId,
      daiReserveId,
      address(liquidationSharesPartialActor),
      100_000e18,
      true
    );
  }

  function liquidationReceiveSharesFull() external {
    spoke.liquidationCall(
      usdxReserveId,
      daiReserveId,
      address(liquidationSharesFullActor),
      type(uint256).max,
      true
    );
  }

  function liquidationReportDeficitFull() external {
    usdxPriceFeed.setPrice(45e6);
    spoke.liquidationCall(
      usdxReserveId,
      daiReserveId,
      address(liquidationDeficitActor),
      type(uint256).max,
      false
    );
  }
}

// ----
// supplyFirst() -> 0
// supplySecondSameReserve() -> 0
// enableCollateral() -> 0
// borrowFirst() -> 0
// borrowSecondSameReserve() -> 0
// getUserAccountData() -> 0
// updateUserRiskPremium() -> 0
// updateUserDynamicConfig() -> 0
// repayPartial() -> 0
// repayFull() -> 0
// withdrawPartial() -> 0
// withdrawFull() -> 0
// liquidationPartial() -> 0
// liquidationFull() -> 0
// liquidationReceiveSharesPartial() -> 0
// liquidationReceiveSharesFull() -> 0
// liquidationReportDeficitFull() -> 0
