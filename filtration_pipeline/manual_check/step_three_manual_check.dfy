// Kept File 1:
// filename: dafny-synthesis_task_id_457_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_457_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 1
// num_lines: 5
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{}
// Kept File 2:
// filename: dafny-synthesis_task_id_598_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_598_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 1
// num_requires: 1
// num_lines: 4
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{}
