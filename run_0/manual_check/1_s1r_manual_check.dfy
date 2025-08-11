// Kept File 1:
// keepToss: KEEP
// filename: dafny-synthesis_task_id_598_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_598_no_hints.dfy
// 0_keepToss: KEEP
// 0_violated: NONE
// 0_reasoning: The specification correctly defines an Armstrong number check for 3-digit numbers with clear naming, appropriate difficulty level, and proper requires/ensures clauses.
// 1_keepToss: KEEP
// 1_violated: NONE
// 1_reasoning: Well-named method with clear purpose to check if a 3-digit number is an Armstrong number, appropriate difficulty level, and includes proper requires/ensures specifications.
// 2_keepToss: KEEP
// 2_violated: NONE
// 2_reasoning: This is a well-defined Armstrong number checker for 3-digit numbers with a clear method name, understandable purpose, appropriate difficulty level, and proper requires/ensures specifications.

method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{}
// Kept File 2:
// keepToss: KEEP
// filename: dafny-synthesis_task_id_399_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_399_no_hints.dfy
// 0_keepToss: KEEP
// 0_violated: NONE
// 0_reasoning: The specification defines a clear bitwise XOR operation on sequences of 32-bit values with appropriate preconditions and postconditions, representing a useful programming problem of moderate difficulty.
// 1_keepToss: KEEP
// 1_violated: NONE
// 1_reasoning: The specification defines a clear bitwise XOR operation on sequences with appropriate preconditions and postconditions, representing a useful programming problem of moderate difficulty.
// 2_keepToss: KEEP
// 2_violated: NONE
// 2_reasoning: The specification defines a clear bitwise XOR operation on sequences with well-chosen names, appropriate difficulty level, and proper requires/ensures clauses that specify the output length matches input and each element is the XOR of corresponding inputs.

method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{}
// Tossed File 1:
// keepToss: TOSS
// filename: Clover_modify_2d_array_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_modify_2d_array_no_hints.dfy
// 0_keepToss: TOSS
// 0_violated: 4, 7
// 0_reasoning: The problem is too trivial (just modifying a single array element) and the ensures clause contains a logical error that contradicts the modifies clause, making the specification unsound.
// 1_keepToss: TOSS
// 1_violated: 4, 6
// 1_reasoning: This is a trivial array element modification operation that lacks complexity and represents only a single isolated method without any conceptually related components working toward a broader goal.
// 2_keepToss: KEEP
// 2_violated: NONE
// 2_reasoning: Clear method for modifying a 2D array element with proper preconditions and postconditions that preserve array structure and only change the target element.
method modify_array_element(arr: array<array<nat>>, index1: nat, index2: nat, val: nat)
  requires index1 < arr.Length
  requires index2 < arr[index1].Length
  requires forall i: nat, j:nat :: i < arr.Length && j < arr.Length && i != j ==> arr[i] != arr[j]
  modifies arr[index1]
  ensures forall i: nat :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures forall i: nat, j: nat :: 0 <= i < arr.Length && 0 <= j < arr[i].Length && (i != index1 || j != index2) ==> arr[i][j] == old(arr[i][j])
  ensures  arr[index1][index2] == val
{}



// Tossed File 2:
// keepToss: TOSS
// filename: dafny-synthesis_task_id_58_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_58_no_hints.dfy
// 0_keepToss: TOSS
// 0_violated: 4
// 0_reasoning: This is a trivial problem that only requires checking two simple boolean conditions, making it too easy for a programming benchmark.
// 1_keepToss: TOSS
// 1_violated: 4
// 1_reasoning: The problem is far too trivial - it only checks if two integers have opposite signs, which is a very basic boolean condition that doesn't require meaningful algorithmic thinking or programming skills.
// 2_keepToss: TOSS
// 2_violated: 4
// 2_reasoning: The problem is too trivial - it only requires implementing a simple boolean condition check with basic arithmetic comparisons, which is too easy for a meaningful benchmark.
method HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{}


