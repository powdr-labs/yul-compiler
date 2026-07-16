// Doubly-recursive Fibonacci. Exercises the calling convention: argument and
// return-value passing, the return-address discipline, and repeated stack-frame
// setup/teardown — the part of a non-optimizing compiler that is furthest from
// solc's inlined, optimized output.
{
    function fib(n) -> r {
        switch lt(n, 2)
        case 1 { r := n }
        default { r := add(fib(sub(n, 1)), fib(sub(n, 2))) }
    }
    sstore(0, fib(15))
}
