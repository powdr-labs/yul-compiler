// Fills a memory buffer word by word, then hashes progressively longer
// prefixes of it. Exercises memory expansion pricing and the per-word keccak256
// cost inside a loop, alongside the usual arithmetic overhead.
{
    for { let i := 0 } lt(i, 32) { i := add(i, 1) }
    {
        mstore(mul(i, 32), add(i, 0xabc))
    }
    let acc := 0
    for { let k := 1 } lt(k, 33) { k := add(k, 1) }
    {
        acc := xor(acc, keccak256(0, mul(k, 32)))
    }
    sstore(0, acc)
}
