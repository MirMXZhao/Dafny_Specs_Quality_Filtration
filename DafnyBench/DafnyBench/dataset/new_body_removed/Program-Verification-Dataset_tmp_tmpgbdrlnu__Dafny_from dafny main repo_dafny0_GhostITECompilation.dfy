// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --function-syntax:4 --relax-definite-assignment

function F(x: nat, ghost y: nat): nat
{}

lemma AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
{
}

function G(x: nat, ghost y: nat): nat
{}

// Ostensibly, the following function is tail recursive. But the ghost-ITE optimization
// removes the tail call. This test ensures that the unused setup for the tail optimization
// does not cause problems.
function H(x: int, ghost y: nat): int {}

// Like function H, function J looks like it's tail recursive. The compiler probably will
// emit the tail-call label, even though the tail-call is never taken.
function J(x: int): int {}

// The following function would never verify, and its execution wouldn't terminate.
// Nevertheless, we'll test here that it compiles into legal target code.
function {:verify false} K(x: int, ghost y: nat): int {
  K(x, y - 1)
}

method Main() {}

