// A calldata-driven dispatch loop: each iteration selects an operation by a
// byte derived from calldata and folds the result. Exercises switch lowering
// and branch-heavy control flow, and — because it reads calldata — produces
// distinct, still fully deterministic, gas figures across the input scenarios.
{
    function op(sel, x, y) -> r {
        switch mod(sel, 4)
        case 0 { r := add(x, y) }
        case 1 { r := mul(add(x, 1), add(y, 1)) }
        case 2 { r := xor(shl(1, x), y) }
        default { r := add(x, div(y, add(mod(x, 7), 1))) }
    }
    let acc := 1
    for { let i := 0 } lt(i, 64) { i := add(i, 1) }
    {
        let sel := byte(0, calldataload(mod(mul(i, 32), 96)))
        acc := op(sel, acc, i)
    }
    sstore(0, acc)
}
