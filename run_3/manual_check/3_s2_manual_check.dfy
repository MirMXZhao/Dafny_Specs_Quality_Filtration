// Kept File 1:
// filename: Clover_two_sum_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_two_sum_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification fully determines the output with precise requires and ensures statements that can be verified by Dafny.

method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{}

// Kept File 2:
// filename: dafny-synthesis_task_id_424_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_424_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification is fully determined by the ensures clauses which completely specify that the output sequence contains the last character of each input string.

method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{}
// Kept File 3:
// filename: Clover_min_of_two_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_min_of_two_no_hints.dfy
// keepToss: KEEP
// reasoning: The ensures clauses fully specify the output by covering all possible cases (x<=y and x>y) and determining the exact value of z in each case.

method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{}

// Kept File 4:
// filename: dafny-synthesis_task_id_809_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_809_no_hints.dfy
// keepToss: KEEP
// reasoning: The ensures statements fully specify the output by defining result as true when all elements of a are greater than corresponding elements of b, and false otherwise.

method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{}
// Kept File 5:
// filename: dafny-synthesis_task_id_750_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_750_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification is fully defined with complete ensures clauses that determine the exact output behavior of the method.

method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
    r := l + [t];
}
// Kept File 6:
// filename: dafny-synthesis_task_id_591_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_591_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification fully determines the behavior of SwapFirstAndLast by ensuring the first and last elements are swapped while all other elements remain unchanged.

method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{}
// Kept File 7:
// filename: Clover_online_max_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_online_max_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification is fully determined by the requires and ensures clauses, defining both the ghost variable m (maximum in prefix) and return value p (position of first element exceeding m).

method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{}


// Kept File 8:
// filename: dafny-synthesis_task_id_808_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_808_no_hints.dfy
// keepToss: KEEP
// reasoning: The method has a complete specification with a fully determining ensures clause that specifies the exact output condition.

method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{}
// Kept File 9:
// filename: stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification is fully specified with complete requires and ensures statements for all methods and functions, defining a priority queue implementation with proper invariants and correctness proofs.

// Ch. 10: Datatype Invariants

module PQueue {
    export
        // Impl
        provides PQueue
        provides Empty, IsEmpty, Insert, RemoveMin
        // Spec
        provides Valid, Elements, EmptyCorrect, IsEmptyCorrect
        provides InsertCorrect, RemoveMinCorrect
        reveals IsMin

    // Implementation
    type PQueue = BraunTree
    datatype BraunTree =
        | Leaf
        | Node(x: int, left: BraunTree, right: BraunTree)

    function Empty(): PQueue {
        Leaf
    }

    predicate IsEmpty(pq: PQueue) {
        pq == Leaf
    }

    function Insert(pq: PQueue, y: int): PQueue {
        match pq
        case Leaf => Node(y, Leaf, Leaf)
        case Node(x, left, right) =>
            if y < x then
                Node(y, Insert(right ,x), left)
            else
                Node(x, Insert(right, y), left)
    }

    function RemoveMin(pq: PQueue): (int, PQueue)
      requires Valid(pq) && !IsEmpty(pq)
    {
        var Node(x, left, right) := pq;
        (x, DeleteMin(pq))
    }
    
    function DeleteMin(pq: PQueue): PQueue
      requires IsBalanced(pq) && !IsEmpty(pq)
    {
        // Ex. 10.4: by the IsBalanced property, pq.left is always as large or one node larger
        // than pq.right. Thus pq.left.Leaf? ==> pq.right.leaf?
        if pq.right.Leaf? then
            pq.left
        else if pq.left.x <= pq.right.x then
            Node(pq.left.x, pq.right, DeleteMin(pq.left))
        else
            Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
    }

    function ReplaceRoot(pq: PQueue, r: int): PQueue
        requires !IsEmpty(pq)
    {
        // left is empty or r is smaller than either sub-root
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        then
            // simply replace the root
            Node(r, pq.left, pq.right)
        // right is empty, left has one element
        else if pq.right.Leaf? then
            Node(pq.left.x, Node(r, Leaf, Leaf), Leaf)
        // both left/right are non-empty and `r` needs to be inserted deeper in the sub-trees
        else if pq.left.x < pq.right.x then
            // promote left root
            Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right)
        else
            // promote right root
            Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))
    }

    //////////////////////////////////////////////////////////////
    // Specification exposed to callers
    //////////////////////////////////////////////////////////////

    ghost function Elements(pq: PQueue): multiset<int> {
        match pq
        case Leaf => multiset{}
        case Node(x, left, right) =>
            multiset{x} + Elements(left) + Elements(right)
    }

    ghost predicate Valid(pq: PQueue) {
        IsBinaryHeap(pq) && IsBalanced(pq)
    }
    
    //////////////////////////////////////////////////////////////
    // Lemmas
    //////////////////////////////////////////////////////////////

    ghost predicate IsBinaryHeap(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(x, left, right) =>
            IsBinaryHeap(left) && IsBinaryHeap(right) &&
            (left.Leaf? || x <= left.x) &&
            (right.Leaf? || x <= right.x)
    }

    ghost predicate IsBalanced(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(_, left, right) =>
            IsBalanced(left) && IsBalanced(right) &&
            var L, R := |Elements(left)|, |Elements(right)|;
            L == R || L == R + 1
    }

    // Ex. 10.2
    lemma {:induction false} BinaryHeapStoresMin(pq: PQueue, y: int)
      requires IsBinaryHeap(pq) && y in Elements(pq)
      ensures pq.x <= y
    {
        if pq.Node? {
                || y in Elements(pq.left) 
                || y in Elements(pq.right));
            if y == pq.x {
            } else if y in Elements(pq.left) {
                BinaryHeapStoresMin(pq.left, y);
            } else if y in Elements(pq.right) {
                BinaryHeapStoresMin(pq.right, y);
            }
        }
    }

    lemma EmptyCorrect()
      ensures Valid(Empty()) && Elements(Empty()) == multiset{}
    { // unfold Empty()
    }
    
    lemma IsEmptyCorrect(pq: PQueue)
      requires Valid(pq)
      ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
    {
        if Elements(pq) == multiset{} {
        }
    }
    
    lemma InsertCorrect(pq: PQueue, y: int)
      requires Valid(pq)
      ensures var pq' := Insert(pq, y);
        Valid(pq') && Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
    {}

    lemma RemoveMinCorrect(pq: PQueue)
      requires Valid(pq)
      requires !IsEmpty(pq)
      ensures var (y, pq') := RemoveMin(pq);
              Elements(pq) == Elements(pq') + multiset{y} &&
              IsMin(y, Elements(pq)) &&
              Valid(pq')
    {
        DeleteMinCorrect(pq);
    }
    
    lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} DeleteMinCorrect(pq: PQueue)
      requires Valid(pq) && !IsEmpty(pq)
      ensures var pq' := DeleteMin(pq);
        Valid(pq') &&
        Elements(pq') + multiset{pq.x} == Elements(pq) &&
        |Elements(pq')| == |Elements(pq)| - 1
    {
        if pq.left.Leaf? || pq.right.Leaf? {}
        else if pq.left.x <= pq.right.x {
            DeleteMinCorrect(pq.left);
        } else {
            var left, right := ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left);
            var pq' := Node(pq.right.x, left, right);
            
            // Elements post-condition
            calc {
                Elements(pq') + multiset{pq.x};
            ==  // defn Elements
                (multiset{pq.right.x} + Elements(left) + Elements(right)) + multiset{pq.x};
            ==  // multiset left assoc
                ((multiset{pq.right.x} + Elements(left)) + Elements(right)) + multiset{pq.x};
            == { ReplaceRootCorrect(pq.right, pq.left.x);
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(right)) + multiset{pq.x};
            ==  // defn right
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(DeleteMin(pq.left))) + multiset{pq.x};
            ==  // multiset right assoc
                (Elements(pq.right) + (multiset{pq.left.x} + Elements(DeleteMin(pq.left)))) + multiset{pq.x};
            == { DeleteMinCorrect(pq.left);
                (Elements(pq.right) + (Elements(pq.left))) + multiset{pq.x};
            ==
                multiset{pq.x} + Elements(pq.right) + (Elements(pq.left));
            ==
                Elements(pq);
            }
            
            // Validity
            // Prove IsBinaryHeap(pq')
            // IsBinaryHeap(left) && IsBinaryHeap(right) &&
            DeleteMinCorrect(pq.left);
            ReplaceRootCorrect(pq.right, pq.left.x);
            
            // (left.Leaf? || x <= left.x) &&
            BinaryHeapStoresMin(pq.left, pq.left.x);
            BinaryHeapStoresMin(pq.right, pq.right.x);
            // (right.Leaf? || x <= right.x)
        }
    }

    lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} ReplaceRootCorrect(pq: PQueue, r: int)
      requires Valid(pq) && !IsEmpty(pq)
      ensures var pq' := ReplaceRoot(pq, r);
        Valid(pq') &&
        r in Elements(pq') &&
        |Elements(pq')| == |Elements(pq)| &&
        Elements(pq) + multiset{r} == Elements(pq') + multiset{pq.x}
    {
        var pq' := ReplaceRoot(pq, r);
        // Element post-condition
        var left, right := pq'.left, pq'.right;
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        {
            // simply replace the root
        }
        else if pq.right.Leaf? {
            // both left/right are non-empty and `r` needs to be inserted deeper in the sub-trees
        }
        else if pq.left.x < pq.right.x {
            // promote left root
            ReplaceRootCorrect(pq.left, r);
            calc {
                Elements(pq') + multiset{pq.x};
            ==
                (multiset{pq.left.x} + Elements(ReplaceRoot(pq.left, r)) + Elements(pq.right)) + multiset{pq.x};
            == { ReplaceRootCorrect(pq.left, r); }
                (Elements(pq.left) + multiset{r}) + Elements(pq.right) + multiset{pq.x};
            ==
                Elements(pq) + multiset{r};
            }
        }
        else {
            // promote right root
            ReplaceRootCorrect(pq.right, r);
            calc {
                Elements(pq') + multiset{pq.x};
            ==  // defn
                (multiset{pq.right.x} + Elements(pq.left) + Elements(ReplaceRoot(pq.right, r))) + multiset{pq.x};
            ==  // assoc
                (Elements(pq.left) + (Elements(ReplaceRoot(pq.right, r)) + multiset{pq.right.x})) + multiset{pq.x};
            == { ReplaceRootCorrect(pq.right, r); }
                (Elements(pq.left) + multiset{r} + Elements(pq.right)) + multiset{pq.x};
            ==
                Elements(pq) + multiset{r};
            }
        }
    }

    ghost predicate IsMin(y: int, s: multiset<int>) {
        y in s && forall x :: x in s ==> y <= x
    }

}

// Ex 10.0, 10.1
module PQueueClient {
    import PQ = PQueue

    method Client() {
        var pq := PQ.Empty();
        PQ.EmptyCorrect();
        PQ.InsertCorrect(pq, 1);
        var pq1 := PQ.Insert(pq, 1);

        PQ.InsertCorrect(pq1, 2);
        var pq2 := PQ.Insert(pq1, 2);

        PQ.IsEmptyCorrect(pq2);
        PQ.RemoveMinCorrect(pq2);
        var (m, pq3) := PQ.RemoveMin(pq2);        

        PQ.IsEmptyCorrect(pq3);
        PQ.RemoveMinCorrect(pq3);
        var (n, pq4) := PQ.RemoveMin(pq3);        

        PQ.IsEmptyCorrect(pq4);

    }
}

// Kept File 10:
// filename: iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
// keepToss: KEEP
// reasoning: This is an abstract module template with predicates, functions, and lemmas that have proper signatures and specifications, even though the implementations are abstract.

// General form of a ShardedStateMachine
// To instantiate one, fill in the 'Shard' type, the 'glue' function
// provide the 'Next' predicate and the invariant 'Inv',
// and then meet various proof obligations in the form of lemmas.

abstract module ShardedStateMachine {
  /*
   * A ShardedStateMachine contains a 'Shard' type that represents
   * a shard of the state machine.
   */

  type Shard

  predicate valid_shard(a: Shard)

  /*
   * There must be some notion that lets us put two shards together.
   */

  function glue(a: Shard, b: Shard) : Shard

  /*
   * The 'glue' operation must respect monoidal laws.
   */

  lemma glue_commutative(a: Shard, b: Shard)
  ensures glue(a, b) == glue(b, a)

  lemma glue_associative(a: Shard, b: Shard, c: Shard)
  ensures glue(glue(a, b), c) == glue(a, glue(b, c))

  function unit() : Shard
  ensures valid_shard(unit())

  lemma glue_unit(a: Shard)
  ensures glue(a, unit()) == a

  /*
   * The invariant is meant to be a predicate over a 'whole' shard,
   * that is, all the pieces glued together at once.
   */

  predicate Inv(s: Shard)

  /*
   * 'Next' predicate of our state machine.
   */

  predicate Next(shard: Shard, shard': Shard)

  lemma NextPreservesValid(s: Shard, s': Shard)
  requires valid_shard(s)
  requires Next(s, s')
  ensures valid_shard(s')

  lemma NextAdditive(s: Shard, s': Shard, t: Shard)
  requires Next(s, s')
  requires valid_shard(glue(s, t))
  requires Next(glue(s, t), glue(s', t))

  /*
   * The operation must preserve the state machine invariant.
   */

  lemma NextPreservesInv(s: Shard, s': Shard)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
}


// Kept File 11:
// filename: dafny-synthesis_task_id_94_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_94_no_hints.dfy
// keepToss: KEEP
// reasoning: The ensures clause fully specifies that the method returns the first element of a sequence that has the minimum second element, which is completely deterministic and verifiable.

method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{}
// Kept File 12:
// filename: Clover_longest_prefix_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_longest_prefix_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification fully determines the output by ensuring the prefix is the longest common prefix of both input sequences.

method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{}

// Kept File 13:
// filename: dafny-synthesis_task_id_262_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_262_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification fully determines the output with clear ensures statements that define the lengths and content of the returned sequences.

method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{}
// Kept File 14:
// filename: Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// keepToss: KEEP
// reasoning: Both methods have complete requires and ensures statements that fully specify their behavior and can be verified by Dafny.

method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}


// Kept File 15:
// filename: cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// keepToss: KEEP
// reasoning: The method has proper requires and modifies clauses that specify the preconditions and what can be modified, making it a valid specification for Dafny verification.

// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 
// The following is just plain old bubble sort.
//
// Can you find the invariants for the while loops?
// Can you annotate this?
// What about the pre/post-conditions?

method BubbleSort(A: array<int>, n: int)
modifies A;
requires A.Length>=0 && n==A.Length;
{}

/*Doesn't my title look all bubbly and cute? I'm trying... */


// Tossed File 1:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example_no_hints.dfy
// keepToss: TOSS
// reasoning: The specification has multiple functions and predicates (contains, min, max, intersect, overlap, union) that are declared but not implemented, making it impossible to verify the correctness of the lemmas that depend on them.
/* Here's a small but realistic setting where you could use Dafny.

   The setting is that we're implementing an interval library that manages a
   data structure with a low and a high value. It implements some computations
   on intervals, and we want to make sure those are right.
 */

// Interval is the Dafny model of the data structure itself. We're using `real`
// here for the numbers; the specifics don't really matter, as long as we can
// compare them with <.
datatype Interval = Interval(lo: real, hi: real)

// Contains is one of the core operations on intervals, both because we support
// it in the API and because in some ways it defines what the interval means.
predicate contains(i: Interval, r: real) {}

// We also provide a way to check if an interval is empty.
predicate empty(i: Interval) {
  i.lo > i.hi
}

/* Now we can already do our first proof! Empty is a way to check if an interval
 * doesn't contain any numbers - let's prove that empty and contains agree with
 * each other. */

lemma empty_ok(i: Interval)
  // this is the sort of property that's easy to express logically but hard to test for
  ensures empty(i) <==> !exists r :: contains(i, r)
{}

// min and max are just helper functions for the implementation
function min(r1: real, r2: real): real {}

function max(r1: real, r2: real): real {}

/* The first complicated operation we expose is a function to intersect two
 * intervals. It's not so easy to think about whether this is correct - for
 * example, does it handle empty intervals correctly? Maybe two empty intervals
 * could intersect to a non-empty one? */

function intersect(i1: Interval, i2: Interval): Interval {}

// This theorem proves that intersect does exactly what we wanted it to, using
// `contains` as the specification.
lemma intersect_ok(i1: Interval, i2: Interval)
  ensures forall r :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
{
}

/* Next we'll define the union of intervals. This is more complicated because if
 * the intervals have no overlap, a single interval can't capture their union
 * exactly. */

// Intersect gives us an easy way to define overlap, and we already know it
// handles empty intervals correctly.
predicate overlap(i1: Interval, i2: Interval) {}

lemma overlap_ok(i1: Interval, i2: Interval)
  ensures overlap(i1, i2) <==> exists r :: contains(i1, r) && contains(i2, r)
{}

// We'll give this function a precondition so that it always does the right thing.
function union(i1: Interval, i2: Interval): Interval
  requires overlap(i1, i2)
{}

// We can prove union correct in much the same way as intersect, with a similar
// specification, although notice that now we require that the intervals
// overlap.
lemma union_ok(i1: Interval, i2: Interval)
  requires overlap(i1, i2)
  ensures forall r :: contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
{
}

// Though not used elsewhere here, if two intervals overlap its possible to show
// that there's a common real contained in both of them. We also show off new
// syntax: this lemma returns a value which is used in the postcondition, and
// which the calling lemma can make use of.
lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  requires overlap(i1, i2)
  ensures contains(i1, r) && contains(i2, r)
{}

/* One extension you might try is adding is an operation to check if an interval
 * is contained in another and proving that correct. Or, try implementing a
 * similar library for 2D rectangles. */




// Tossed File 2:
// filename: MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_no_hints.dfy
// keepToss: TOSS
// reasoning: The function power(x, n) has no body or ensures clause, making the specifications of powerIter and powerOpt not fully specified since they depend on an undefined function.
/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{}

// A simple test case to make sure the specification is adequate.
method testPowerIter(){}

method testPowerOpt(){}



// Tossed File 3:
// filename: SENG2011_tmp_tmpgk5jq85q_flex_ex2_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/SENG2011_tmp_tmpgk5jq85q_flex_ex2_no_hints.dfy
// keepToss: TOSS
// reasoning: The function maxcheck has no ensures clause to specify what it should return, making it not fully specified.
function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{}

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{}

method Checker() {}



// Tossed File 4:
// filename: dafny-duck_tmp_tmplawbgxjo_p6_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-duck_tmp_tmplawbgxjo_p6_no_hints.dfy
// keepToss: TOSS
// reasoning: The vowels set is empty and the FilterVowels function body is not defined, making the specification not fully specified.
//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {}

function FilterVowels(xs: seq<char>): seq<char>
{}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{}



// Tossed File 5:
// filename: FMSE-2022-2023_tmp_tmp6_x_ba46_Lab1_Lab1_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/FMSE-2022-2023_tmp_tmp6_x_ba46_Lab1_Lab1_no_hints.dfy
// keepToss: TOSS
// reasoning: The predicates and functions lack body implementations and ensures clauses that fully specify their behavior, making them unverifiable by Dafny.
/// Types defined as part of Tasks 3, 5 and 9

// Since we have created the IsOddNat predicate we use it to define the new Odd subsort
newtype Odd = n : int | IsOddNat(n) witness 1

// Since we have created the IsEvenNat predicate we use it to define the new Even subsort
newtype Even = n : int | IsEvenNat(n) witness 2

/*
 * We use int as the native type, so that the basic operations are available. 
 * However, we restrict the domain in order to accomodate the requirements.
 */
newtype int32 = n: int | -2147483648 <= n < 2147483648 witness 3

/// Task 2

/*
 * In order for an integer to be a natural, odd number, two requirements must be satisfied:
 * The integer in cause must be positive and the remainder of the division by 2 must be 1.
 */
predicate IsOddNat(x: int) {}

/// Task 4

/*
 * In order for an integer to be a natural, even number, two requirements must be satisfied:
 * The integer in cause must be positive and the remainder of the division by 2 must be 0.
 */
predicate IsEvenNat(x: int) {}

/// Task 6

/*
 * In order to prove the statement, we rewrite the two numbers to reflect their form:
 * The sum between a multiple of 2 and 1.
 *
 * By rewriting them like this and then adding them together, the sum is shown to
 * be a multiple of 2 and thus, an even number.
 */
lemma AdditionOfTwoOddsResultsInEven(x: int, y: int) 
    requires IsOddNat(x);
    requires IsOddNat(y);
    ensures IsEvenNat(x + y);
{}

/// Task 7
/*
 * In order for an integer to be a natural, prime number, two requirements must be satisfied:
 * The integer in cause must be natural (positive) and must have exactly two divisors:
 * 1 and itself.
 *
 * Aside from two, which is the only even prime, we test the primality by checking if there
 * is no number greater or equal to 2 that the number in cause is divisible with.
 */
predicate IsPrime(x: int)
    requires x >= 0;
{}

/// Task 8
/*
 * It is a known fact that any prime divided by any number, aside from 1 and itself,
 * will yield a non-zero remainder.
 * 
 * Thus, when dividing a prime (other than 2) by 2, the only non-zero remainder possible 
 * is 1, therefore making the number an odd one.
 */
lemma AnyPrimeGreaterThanTwoIsOdd(x : int)
    requires x > 2;
    requires IsPrime(x);
    ensures IsOddNat(x);
{}

/* 
 * Task 9 
 * Defined the basic arithmetic functions.
 * Also defined the absolute value.
 * 
 * Over/Underflow are represented by the return of 0.
 */
function add(x: int32, y: int32): int32 {}

function sub(x: int32, y: int32): int32 {}

function mul(x: int32, y: int32): int32 {}

function div(x: int32, y: int32): int32 
    requires y != 0; 
{}

function mod(x: int32, y: int32): int32
    requires y != 0; 
{}

function abs(x: int32): (r: int32)
    ensures r >= 0;
{}




// Tossed File 6:
// filename: Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower_no_hints.dfy
// keepToss: TOSS
// reasoning: The function Power is not defined, so the ensures clause cannot be verified by Dafny.
function Power(n: nat): nat {}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{}



// Tossed File 7:
// filename: CVS-handout1_tmp_tmptm52no3k_2_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/CVS-handout1_tmp_tmptm52no3k_2_no_hints.dfy
// keepToss: TOSS
// reasoning: The functions length, mem, and at have no body or ensures clauses, making them not fully specified.
/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes        57854
*/

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function length<T>(l: List<T>): nat
{}

predicate mem<T(==)> (l: List<T>, x: T)
{}

function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
{}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{}

method Main() {}



// Tossed File 8:
// filename: veri-sparse_tmp_tmp15fywna6_dafny_concurrent_poc_6_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/veri-sparse_tmp_tmp15fywna6_dafny_concurrent_poc_6_no_hints.dfy
// keepToss: TOSS
// reasoning: The function `sum` is not defined in its body, making the specification not fully specified since the ensures statements cannot be verified without knowing how sum is computed.
class Process {}

function sum(s : seq<nat>) : nat
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
{}

lemma sum0(s : seq<nat>)
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
  {}

lemma sum_const(s : seq<nat>, x : nat)
  ensures (forall i :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x 
  {
  }

lemma sum_eq(s1 : seq<nat>, s2 : seq<nat>)
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
  ensures sum(s1) == sum(s2)
  {

  }

lemma sum_exept(s1 : seq<nat>, s2 : seq<nat>, x : nat, j : nat)
requires |s1| == |s2|
requires j < |s1|
requires forall i :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
requires s1[j] == s2[j] + x
ensures sum(s1) == sum(s2) + x
{}


function calcRow(M : array2<int>, x : seq<int>, row: nat, start_index: nat) : (product: int)
    reads M
    requires M.Length1 == |x|
    requires row < M.Length0
    requires start_index <= M.Length1
{}

class MatrixVectorMultiplier
{   

    ghost predicate Valid(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers : array<nat>)
        reads this, y, P, M, leftOvers
    {}


    constructor (processes: set<Process>, M_: array2<int>, x_: seq<int>, y_: array<int>, leftOvers : array<nat>)
        // Idea here is that we already have a set of processes such that each one is assigned one row.
        // Daphny makes it a ginormous pain in the ass to actually create such a set, so we just assume
        // we already have one.

        //this states that the number of rows and processes are the same, and that there is one process
        //for every row, and that no two processes are the same, nor do any two processes share the same
        //row
        requires (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        requires |processes| == leftOvers.Length 
        requires |processes| == M_.Length0
        requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
        requires (forall p, q :: p in processes && q in processes ==> p != q)
        requires (forall p :: p in processes ==> 0 <= p.row < M_.Length0)

        //initializes process start
        requires (forall p :: p in processes ==> 0 == p.curColumn)
        requires (forall p :: p in processes ==> p.opsLeft == M_.Length1)

        requires (forall i :: 0 <= i < y_.Length ==> y_[i] == 0)
        requires y_.Length == M_.Length0

        requires |x_| == M_.Length1
        requires M_.Length0 > 0
        requires |x_| > 0
        ensures (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        ensures Valid(M_, x_, y_, processes, leftOvers)
    {
        
    }

    method processNext(M: array2<int>, x: seq<int>, y: array<int>, P : set<Process>, leftOvers : array<nat>)
        requires Valid(M, x, y, P, leftOvers)
        requires exists p :: (p in P && p.opsLeft > 0)
        requires sum(leftOvers[..]) > 0
        modifies this, y, P, leftOvers
        requires (forall p, q :: p in P && q in P && p != q ==> p.row != q.row)

        ensures Valid(M, x, y, P, leftOvers)
        ensures sum(leftOvers[..]) == sum(old(leftOvers[..])) - 1
    {}


}

method Run(processes: set<Process>, M: array2<int>, x: array<int>) returns (y: array<int>)
    requires |processes| == M.Length0
    requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
    requires (forall p, q :: p in processes && q in processes ==> p != q)
    requires (forall p :: p in processes ==> 0 <= p.row < M.Length0)

    requires (forall p :: p in processes ==> 0 == p.curColumn)
    requires (forall p :: p in processes ==> p.opsLeft == M.Length1)

    requires x.Length > 0
    requires M.Length0 > 0
    requires M.Length1 == x.Length
    ensures M.Length0 == y.Length
    modifies processes, M, x
{}


// lemma lemma_newProcessNotInSet(process: Process, processes: set<Process>)
//     requires (forall p :: p in processes ==> p.row != process.row)
//     ensures process !in processes
// {
// }

// lemma diffRowMeansDiffProcess(p1: Process, p2: Process)
//     requires p1.row != p2.row
//     ensures p1 != p2
// {
// }


// method createSetProcesses(numRows: nat, numColumns: nat) returns (processes: set<Process>)
//     ensures |processes| == numRows
//     ensures (forall p, q :: p in processes && q in processes ==> p != q)
//     ensures (forall p, q :: p in processes && q in processes && p != q ==> p.row != q.row)
//     ensures (forall p :: p in processes ==> 0 <= p.row < numRows)
//     ensures (forall p :: p in processes ==> 0 == p.curColumn)
//     ensures (forall p :: p in processes ==> p.opsLeft == numColumns)
// {}

// method Main()
// {}




// Tossed File 9:
// filename: feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// keepToss: TOSS
// reasoning: The predicate isSorted has an empty body, making the specification not fully specified since it doesn't define what it means for an array to be sorted.
/* 
* Formal verification of the selection sort algorithm with Dafny.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{}

// Sorts array 'a' using the selection sort algorithm.
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

method testSelectionSort() {}

method testFindMin() {}



// Tossed File 10:
// filename: Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Quick_Sort_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Quick_Sort_no_hints.dfy
// keepToss: TOSS
// reasoning: The quickSorted predicate is not defined, and the quickSort method does not ensure the output is sorted, making the specification incomplete.
predicate quickSorted(Seq: seq<int>)
{}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{}


lemma Lemma_1(Seq_1:seq,Seq_2:seq)  // The proof of the lemma is not necessary
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2

{}



method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
{}









// Tossed File 11:
// filename: SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// keepToss: TOSS
// reasoning: The ensures clause specifies that all elements must be even, but there's no specification of what the method should do to achieve this (e.g., whether to modify existing elements, how to handle odd numbers, etc.), making it not fully specified.
// successfully verifies
method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{}



// Tossed File 12:
// filename: dafny-synthesis_task_id_566_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_566_no_hints.dfy
// keepToss: TOSS
// reasoning: The specification contains multiple functions (SumDigits, Power10, NumberToSeq, Sum, SumDigitsRecursive, NumberOfDigits, IntValues) that have no body and their ensures clauses do not fully specify their behavior, making verification impossible.
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{}

//lemma DivIsZero()
//  ensures forall num, den : nat :: den >= 1 && num < den ==> num/den == 0

lemma X(x: nat)
  ensures Power10(NumberOfDigits(x)) > x
{}

lemma NumberIdentity(number: nat, pmax: nat)
  requires pmax == Power10(NumberOfDigits(number))
  ensures number == number % pmax
{}


lemma InIntValues(n: nat)
  ensures 0 in IntValues(n)
  ensures n in IntValues(n)
  ensures n/10 in IntValues(n)
{}

// ghost function ValuesOfn(number: nat, ndigits: nat) : (r: seq<nat>)
// {}

ghost function IntValues(n: int) : (r: seq<int>)
  requires n >= 0
  ensures 0 in r
  ensures n in r
  ensures n/10 in r
  //    ensures forall p :: p in powersOfTen ==> n/p in r
{}

function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{}

function NumberToSeq(number: int) : seq<int>
  requires number >= 0
{}

function Sum(digits: seq<int>) : int
{}

function SumDigits(n: nat) : nat
{}

function SumDigitsRecursive(n: nat, p: nat) : (r: nat)
{}

function NumberOfDigits(n: nat) : (r: nat)
  ensures r >= 1
  ensures r == 1 <==> 0 <= n <= 9
{}


// Tossed File 13:
// filename: dafny-synthesis_task_id_401_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_401_no_hints.dfy
// keepToss: TOSS
// reasoning: The ensures statements contradict each other - one states result[i] == a[i] while another states result[i][j] == a[i][j] + b[i][j], making the specification inconsistent and not fully determined.
method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
{}


// Tossed File 14:
// filename: dafny-synthesis_task_id_2_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_2_no_hints.dfy
// keepToss: TOSS
// reasoning: The predicate InArray is not defined (empty body), so the ensures statements cannot be properly verified by Dafny.
predicate InArray(a: array<int>, x: int)
    reads a
{}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}


// Tossed File 15:
// filename: Software-Verification_tmp_tmpv4ueky2d_Remove Duplicates from Sorted Array_remove_duplicates_from_sorted_array_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Software-Verification_tmp_tmpv4ueky2d_Remove Duplicates from Sorted Array_remove_duplicates_from_sorted_array_no_hints.dfy
// keepToss: TOSS
// reasoning: The helper predicates is_sorted and is_sorted_and_distinct are not defined, making the specification unverifiable.
method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{}


// Helper predicate
predicate is_sorted(nums: seq<int>)
{}

predicate is_sorted_and_distinct(nums: seq<int>)
{}




