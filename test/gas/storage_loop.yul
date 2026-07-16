// Storage-dominated loop: repeated SSTORE/SLOAD across many slots, then a
// second pass that overwrites and clears some of them. Exercises cold/warm
// slot pricing and SSTORE refunds, where absolute gas is large and codegen
// differences in address arithmetic are visible.
{
    let acc := 0
    for { let i := 0 } lt(i, 64) { i := add(i, 1) }
    {
        sstore(i, add(i, 1))
        acc := add(acc, sload(i))
    }
    for { let j := 0 } lt(j, 64) { j := add(j, 2) }
    {
        sstore(j, 0)
    }
    sstore(0x100, acc)
}
