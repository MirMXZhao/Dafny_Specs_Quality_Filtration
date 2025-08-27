// Kept File 1:
// filename: 11_dafny-exercise_tmp_tmpouftptir_prac4_ex2_no_hints.dfy
// filepath: ./run_4/new_filtered/11_dafny-exercise_tmp_tmpouftptir_prac4_ex2_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate triple(a: array<int>) 
reads a
{}

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{}
// Kept File 2:
// filename: 18_Clover_online_max_no_hints.dfy
// filepath: ./run_4/new_filtered/18_Clover_online_max_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{}
// Kept File 3:
// filename: 30_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Quick_Sort_no_hints.dfy
// filepath: ./run_4/new_filtered/30_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Quick_Sort_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate quickSorted(Seq: seq<int>)
{}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{}

lemma Lemma_1(Seq_1:seq,Seq_2:seq)
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2
{}

method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
{}
// Kept File 4:
// filename: 24_dafny-synthesis_task_id_2_no_hints.dfy
// filepath: ./run_4/new_filtered/24_dafny-synthesis_task_id_2_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate InArray(a: array<int>, x: int)
    reads a
{}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}
// Kept File 5:
// filename: 21_Clover_rotate_no_hints.dfy
// filepath: ./run_4/new_filtered/21_Clover_rotate_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
{}
// Kept File 6:
// filename: 39_dafny_experiments_tmp_tmpz29_3_3i_circuit_no_hints.dfy
// filepath: ./run_4/new_filtered/39_dafny_experiments_tmp_tmpz29_3_3i_circuit_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

module Base
{
    datatype INodePort = inodeport(node_id: nat, port_id: nat)
    datatype ONodePort = onodeport(node_id: nat, port_id: nat)

    datatype Node =
        Xor |
        And |
        Ident

    function n_iports (node: Node): nat
    {}

    function n_oports (node: Node): nat
    {}

    datatype Circuit = Circ(
        nodes: seq<Node>,
        backconns: map<INodePort, ONodePort>
        )

    predicate WellformedBackConns(c: Circuit)
    {}

    predicate WellformedINP(c: Circuit, inp: INodePort)
    {}

    predicate WellformedONP(c: Circuit, onp: ONodePort)
    {}

    function AllINPs(c: Circuit): set<INodePort>
        ensures forall inp :: inp in AllINPs(c) ==> WellformedINP(c, inp)
    {}

    function AllONPs(c: Circuit): set<ONodePort>
        ensures forall onp :: onp in AllONPs(c) ==> WellformedONP(c, onp)
    {}

    ghost predicate Wellformed(c: Circuit)
    {}
}

module Utils
{}

module BackwardConnections
{
    import opened Base
    import opened Utils

    // This is used when we are trying to create a new circuit by combining two existing circuits.
    // This function takes care of combining the backwards connections.
    // Because the node_indices of the two circuits are just natural numbers when we combine the
    // two circuits we need to shift the node indices of the second circuit so that they don't clash.
    // We do this by adding `offset` to the node indices.
    function CombineBackconns(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>): (result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
    {}

    lemma CombineBackconnsHelper(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        ensures
            forall inp :: inp in bc1 ==> (
                inp in result &&
                result[inp] == bc1[inp])
        ensures
            forall inp :: inp in bc2 ==> (
                inodeport(inp.node_id+offset, inp.port_id) in result &&
                result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id))
    {}

    lemma CombineBackconnsHelper2(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>, inp: INodePort)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        requires inp in bc2
        ensures
            inodeport(inp.node_id+offset, inp.port_id) in result
        ensures
            result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id)
    {}
}


module CombineCircuits {

    import opened Base
    import BackwardConnections
    import opened Utils

    // Combine two circuits into a new circuit.
    // This is a bit ugly because we have to offset the node indices of the
    // second circuit by |c1.nodes|.
    function CombineCircuits(c1: Circuit, c2: Circuit): (r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {}

    // Check that Circuit c2 contains a subcircuit that corresponds to c1 getting mapped with the
    // `node_map` function.
    predicate IsEquivalentCircuit(node_is_member: nat->bool, node_map: nat-->nat, c1: Circuit, c2: Circuit)
        requires forall inp :: inp in c1.backconns && node_is_member(inp.node_id) ==> node_is_member(c1.backconns[inp].node_id)
        requires forall n :: node_is_member(n) ==> node_map.requires(n)
    {}

    // Check that for every input port and output port in the combined Circuit, they can be assigned
    // to a port in one of the two source circuits.
    predicate CanBackAssign(c1: Circuit, c2: Circuit, r: Circuit, is_in_c1: nat->bool, is_in_c2: nat-> bool,
                            map_r_to_c1: nat->nat, map_r_to_c2: nat-->nat)
        requires forall a :: is_in_c1(a) ==> map_r_to_c1.requires(a)
        requires forall a :: is_in_c2(a) ==> map_r_to_c2.requires(a)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {}

    lemma CombineCircuitsCorrectHelper(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
    {}


    lemma CombineCircuitsCorrectC1(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1)
    {
    }

    lemma CombineCircuitsCorrect(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1) &&
            IsEquivalentCircuit(a=>true, a=>a+offset, c2, r) &&
            true
    {}
}
// Kept File 7:
// filename: 35_cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// filepath: ./run_4/new_filtered/35_cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method BubbleSort(A: array<int>, n: int)
modifies A;
requires A.Length>=0 && n==A.Length;
{}
// Kept File 8:
// filename: 27_dafny-synthesis_task_id_733_no_hints.dfy
// filepath: ./run_4/new_filtered/27_dafny-synthesis_task_id_733_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{}
// Kept File 9:
// filename: 25_dafny-synthesis_task_id_732_no_hints.dfy
// filepath: ./run_4/new_filtered/25_dafny-synthesis_task_id_732_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate IsSpaceCommaDot(c: char)
{}

method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{}
// Kept File 10:
// filename: 36_dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array_no_hints.dfy
// filepath: ./run_4/new_filtered/36_dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method foo (s: seq<int>)
requires |s| > 1
{
    print s[1];
}
// Kept File 11:
// filename: 32_Clover_min_of_two_no_hints.dfy
// filepath: ./run_4/new_filtered/32_Clover_min_of_two_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{}
// Kept File 12:
// filename: 3_dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Requires_no_hints.dfy
// filepath: ./run_4/new_filtered/3_dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Requires_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate valid(x:int)
{
  x > 0
}

function ref1(y:int) : int
  requires valid(y);
{
  y - 1
}

lemma assumption1()
  ensures forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
{
}

function {:opaque} ref2(y:int) : int
  requires valid(y);
{
  y - 1
}

lemma assumption2()
  ensures forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
{
  reveal ref2();
}
// Kept File 13:
// filename: 37_feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// filepath: ./run_4/new_filtered/37_feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{}

method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{}

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{}
// Kept File 14:
// filename: 34_SENG2011_tmp_tmpgk5jq85q_flex_ex2_no_hints.dfy
// filepath: ./run_4/new_filtered/34_SENG2011_tmp_tmpgk5jq85q_flex_ex2_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{}

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{}
// Kept File 15:
// filename: 10_dafny-synthesis_task_id_591_no_hints.dfy
// filepath: ./run_4/new_filtered/10_dafny-synthesis_task_id_591_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{}
