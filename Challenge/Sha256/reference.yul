// SHA-256 (FIPS 180-4) as a drop-in replacement for the precompile at 0x02.
//
// Interface, matching the precompile exactly:
//   calldata   = the message, any length
//   returndata = the 32-byte big-endian digest
// The program never reverts and reads nothing but calldata.
//
// This is the *reference* implementation of the yul-compiler SHA-256
// challenge: it is written for provability, not for gas. The hash state and
// the message schedule live in memory so that at most a handful of Yul
// variables are live at once, which keeps every stack access shallow and
// every loop body a short, independently-verifiable memory transformer.
//
// Memory layout (byte offsets):
//   0x000 .. 0x01f   digest output word
//   0x020 .. 0x11f   K[0..63], packed big-endian, 4 bytes each
//   0x120 .. 0x21f   H[0..7], one 32-byte word each (32-bit values)
//   0x220 .. 0x31f   the H of the previous block, for the final addition
//   0x320 .. 0xb1f   W[0..63], one 32-byte word each (32-bit values)
//   0xb20 ..         the padded message
{
    function rotr(x, n) -> r {
        r := and(or(shr(n, x), shl(sub(32, n), x)), 0xffffffff)
    }

    // sigma0/sigma1 of the message schedule (FIPS 180-4 4.6, 4.7)
    function ssig0(x) -> r { r := xor(xor(rotr(x, 7), rotr(x, 18)), shr(3, x)) }
    function ssig1(x) -> r { r := xor(xor(rotr(x, 17), rotr(x, 19)), shr(10, x)) }

    // Sigma0/Sigma1 of the compression rounds (FIPS 180-4 4.4, 4.5)
    function bsig0(x) -> r { r := xor(xor(rotr(x, 2), rotr(x, 13)), rotr(x, 22)) }
    function bsig1(x) -> r { r := xor(xor(rotr(x, 6), rotr(x, 11)), rotr(x, 25)) }

    // Ch and Maj (FIPS 180-4 4.2, 4.3)
    function ch(x, y, z) -> r { r := xor(and(x, y), and(not(x), z)) }
    function maj(x, y, z) -> r { r := xor(xor(and(x, y), and(x, z)), and(y, z)) }

    // K[j]: the four packed bytes at 0x20 + 4*j, read as a big-endian word.
    function kAt(j) -> k { k := shr(224, mload(add(0x20, mul(j, 4)))) }

    // W[j] and H[i] accessors: one 32-byte slot per 32-bit value.
    function wAt(j) -> w { w := mload(add(0x320, mul(j, 32))) }
    function wSet(j, v) { mstore(add(0x320, mul(j, 32)), v) }
    function hAt(i) -> h { h := mload(add(0x120, mul(i, 32))) }
    function hSet(i, v) { mstore(add(0x120, mul(i, 32)), v) }

    // The 64 round constants, eight per 32-byte word.
    function initK() {
        mstore(0x20, 0x428a2f9871374491b5c0fbcfe9b5dba53956c25b59f111f1923f82a4ab1c5ed5)
        mstore(0x40, 0xd807aa9812835b01243185be550c7dc372be5d7480deb1fe9bdc06a7c19bf174)
        mstore(0x60, 0xe49b69c1efbe47860fc19dc6240ca1cc2de92c6f4a7484aa5cb0a9dc76f988da)
        mstore(0x80, 0x983e5152a831c66db00327c8bf597fc7c6e00bf3d5a7914706ca635114292967)
        mstore(0xa0, 0x27b70a852e1b21384d2c6dfc53380d13650a7354766a0abb81c2c92e92722c85)
        mstore(0xc0, 0xa2bfe8a1a81a664bc24b8b70c76c51a3d192e819d6990624f40e3585106aa070)
        mstore(0xe0, 0x19a4c1161e376c082748774c34b0bcb5391c0cb34ed8aa4a5b9cca4f682e6ff3)
        mstore(0x100, 0x748f82ee78a5636f84c878148cc7020890befffaa4506cebbef9a3f7c67178f2)
    }

    // H^(0): the first 32 bits of the fractional parts of the square roots of
    // the first eight primes (FIPS 180-4 5.3.3).
    function initH() {
        hSet(0, 0x6a09e667)
        hSet(1, 0xbb67ae85)
        hSet(2, 0x3c6ef372)
        hSet(3, 0xa54ff53a)
        hSet(4, 0x510e527f)
        hSet(5, 0x9b05688c)
        hSet(6, 0x1f83d9ab)
        hSet(7, 0x5be0cd19)
    }

    // Copy the message to 0xb20 and append the FIPS padding: the 0x80
    // sentinel, zeros (memory is already zero there), and the 64-bit
    // big-endian bit length in the last eight bytes of the last block.
    // Returns the padded length, a multiple of 64.
    function pad() -> paddedLen {
        let n := calldatasize()
        // the smallest multiple of 64 that is at least n + 9
        paddedLen := mul(div(add(n, 72), 64), 64)
        calldatacopy(0xb20, 0, n)
        mstore8(add(0xb20, n), 0x80)
        let bitLen := mul(n, 8)
        let lenOff := add(0xb20, sub(paddedLen, 8))
        for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
            mstore8(add(lenOff, i), and(shr(mul(8, sub(7, i)), bitLen), 0xff))
        }
    }

    // W[0..15] from the block at msgOff, W[16..63] from the recurrence.
    function schedule(msgOff) {
        for { let j := 0 } lt(j, 16) { j := add(j, 1) } {
            wSet(j, shr(224, mload(add(msgOff, mul(j, 4)))))
        }
        for { let j := 16 } lt(j, 64) { j := add(j, 1) } {
            wSet(j, and(add(add(ssig1(wAt(sub(j, 2))), wAt(sub(j, 7))),
                            add(ssig0(wAt(sub(j, 15))), wAt(sub(j, 16)))),
                        0xffffffff))
        }
    }

    // One 64-round compression over the block at msgOff, updating H in place.
    function compress(msgOff) {
        schedule(msgOff)
        // save H^(i-1) for the final addition
        mcopy(0x220, 0x120, 0x100)
        for { let j := 0 } lt(j, 64) { j := add(j, 1) } {
            let e := hAt(4)
            let t1 := and(add(add(add(hAt(7), bsig1(e)),
                                  add(ch(e, hAt(5), hAt(6)), kAt(j))),
                              wAt(j)),
                          0xffffffff)
            let a := hAt(0)
            let t2 := and(add(bsig0(a), maj(a, hAt(1), hAt(2))), 0xffffffff)
            hSet(7, hAt(6))
            hSet(6, hAt(5))
            hSet(5, e)
            hSet(4, and(add(hAt(3), t1), 0xffffffff))
            hSet(3, hAt(2))
            hSet(2, hAt(1))
            hSet(1, a)
            hSet(0, and(add(t1, t2), 0xffffffff))
        }
        for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
            hSet(i, and(add(hAt(i), mload(add(0x220, mul(i, 32)))), 0xffffffff))
        }
    }

    initK()
    initH()
    let paddedLen := pad()
    for { let off := 0 } lt(off, paddedLen) { off := add(off, 64) } {
        compress(add(0xb20, off))
    }
    mstore(0, or(or(or(shl(224, hAt(0)), shl(192, hAt(1))),
                    or(shl(160, hAt(2)), shl(128, hAt(3)))),
                 or(or(shl(96, hAt(4)), shl(64, hAt(5))),
                    or(shl(32, hAt(6)), hAt(7)))))
    return(0, 32)
}
