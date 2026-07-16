// A tight counted loop over pure word arithmetic. Exercises loop lowering and
// the stack shuffling a non-optimizing compiler emits around each operation,
// with no storage or memory traffic to dominate the figure.
{
    let acc := 0
    for { let i := 0 } lt(i, 256) { i := add(i, 1) }
    {
        acc := add(acc, mul(i, i))
        acc := xor(acc, shl(3, i))
    }
    sstore(0, acc)
}
