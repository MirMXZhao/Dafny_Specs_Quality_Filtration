// Kept File 1:
// filename: dafny-synthesis_task_id_290_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_290_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
{}
// Kept File 2:
// filename: Clover_copy_part_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_copy_part_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{}

// Kept File 3:
// filename: SENG2011_tmp_tmpgk5jq85q_exam_ex2_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/SENG2011_tmp_tmpgk5jq85q_exam_ex2_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length // mini is an index of a
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{}

/*
method check() {}
*/


// Kept File 4:
// filename: Clover_double_array_elements_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_double_array_elements_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method double_array_elements(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
{}
// Kept File 5:
// filename: dafny-synthesis_task_id_273_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_273_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
{}
// Kept File 6:
// filename: dafny-synthesis_task_id_240_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_240_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
    requires |first| > 0
    ensures |result| == |first| - 1 + |second|
    ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
    ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{}
// Kept File 7:
// filename: Clover_replace_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_replace_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
{}

// Kept File 8:
// filename: dafny-synthesis_task_id_733_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_733_no_hints.dfy
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
// filename: Clover_canyon_search_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_canyon_search_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{}


// Kept File 10:
// filename: dafny-synthesis_task_id_594_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_594_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
{}
// Kept File 11:
// filename: Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}

method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


// Kept File 12:
// filename: dafny-synthesis_task_id_399_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_399_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{}
// Kept File 13:
// filename: AssertivePrograming_tmp_tmpwf43uz0e_DivMode_Unary_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/AssertivePrograming_tmp_tmpwf43uz0e_DivMode_Unary_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

// Noa Leron 207131871
// Tsuri Farhana 315016907


// definitions borrowed from Rustan Leino's Program Proofs Chapter 7
// (https://program-proofs.com/code.html example code in Dafny; source file 7-Unary.dfy)
datatype Unary = Zero | Suc(pred: Unary)

ghost function UnaryToNat(x: Unary): nat {}

ghost function NatToUnary(n: nat): Unary {}

lemma NatUnaryCorrespondence(n: nat, x: Unary)
  ensures UnaryToNat(NatToUnary(n)) == n
  ensures NatToUnary(UnaryToNat(x)) == x
{
}

predicate Less(x: Unary, y: Unary) {}

predicate LessAlt(x: Unary, y: Unary) {}

lemma LessSame(x: Unary, y: Unary)
  ensures Less(x, y) == LessAlt(x, y)
{
}

lemma LessCorrect(x: Unary, y: Unary)
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
{
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
}

function Add(x: Unary, y: Unary): Unary {}

lemma {:induction false} SucAdd(x: Unary, y: Unary)
  ensures Suc(Add(x, y)) == Add(Suc(x), y)
{}

lemma {:induction false} AddZero(x: Unary)
  ensures Add(Zero, x) == x
{}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{}

function Mul(x: Unary, y: Unary): Unary {}

lemma SubStructurallySmaller(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures Sub(x, y) < x
{
}

lemma AddSub(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(Sub(x, y), y) == x
{
}

/*
Goal: implement correcly and clearly, using iterative code (no recursion), documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal

- DO NOT modify the specification or any of the definitions given in this file
- Not all definitions above are relevant, some are simply included as examples
- Feel free to use existing non-ghost functions/predicates in your code, and existing lemmas (for the proof) in your annotations
- New functions/predicates may be added ONLY as ghost
- If it helps you in any way, a recursive implementation + proof can be found in the book and the downloadable source file
  [https://program-proofs.com/code.html example code in Dafny, source file 7-Unary.dfy]
*/

method{:verify false} IterativeDivMod'(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
{}

method IterativeDivMod(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
{}

lemma AddMulEqMulSuc(a: Unary, b: Unary)
  ensures Mul(Suc(a), b) == Add(Mul(a, b), b)
{}

lemma AddMulSucSubEqAddMul(d: Unary, y: Unary, x0: Unary)
  requires !Less(x0, y)
  requires y != Zero
  ensures Add(Mul(Suc(d), y), Sub(x0, y)) == Add(Mul(d, y), x0)
{
  calc{
    Add(Mul(Suc(d), y), Sub(x0, y));
    == {AddMulEqMulSuc(d, y);
    Add(Add(Mul(d, y), y), Sub(x0, y));
    == {AddTransitive(Mul(d, y), y, Sub(x0, y));
    Add(Mul(d, y), Add(y, Sub(x0, y)));
    == {AddCommutative(Sub(x0, y), y);
    Add(Mul(d, y), Add(Sub(x0, y), y));
    == {assert !Less(x0, y);
        AddSub(x0, y);
    Add(Mul(d, y), x0);
  }
}

lemma AddTransitive(a: Unary, b: Unary, c: Unary)
  ensures Add(a, Add(b, c)) == Add(Add(a, b), c)
{//These assertions are only for documanting the proof obligations
  match c 
  case Zero =>
    calc{
      Add(a, Add(b, c));
      == 
      Add(a, Add(b, Zero));
      == // def. Add
      Add(a, b);
      == // def. Add
      Add(Add(a,b), Zero);
      == 
      Add(Add(a,b), c);
    }
  case Suc(c') =>
    match b
    case Zero =>
      calc{
        Add(a, Add(b, c));
        == 
        Add(a, Add(Zero, Suc(c')));
        == {AddZero(Suc(c'));
        Add(a, Suc(c'));
        == // def. Add
        Add(Add(a, Zero), Suc(c'));
        ==
        Add(Add(a, b), Suc(c'));
        ==
        Add(Add(a,b), c);
      }
    case Suc(b') =>
      match a
      case Zero =>
        calc{
          Add(a, Add(b, c));
          ==
          Add(Zero, Add(Suc(b'), Suc(c')));
          == {AddZero(Add(Suc(b'), Suc(c')));
          Add(Suc(b'), Suc(c'));
          == {AddZero(Suc(b'));
          Add(Add(Zero, Suc(b')), Suc(c'));
          ==
          Add(Add(a, b), c);
        }
      case Suc(a') =>
        calc{
          Add(a, Add(b, c));
          ==
          Add(Suc(a'), Add(Suc(b'), Suc(c')));
          == // def. Add
          Add(Suc(a'), Suc(Add(Suc(b'), c')));
          == // def. Add
          Suc(Add(Suc(a'), Add(Suc(b'), c')));
          == {SucAdd(a', Add(Suc(b'), c'));
          Suc(Suc(Add(a', Add(Suc(b'), c'))));
          == {SucAdd(b', c');
          Suc(Suc(Add(a', Suc(Add(b', c')))));
          == // def. Add
          Suc(Suc(Suc(Add(a', Add(b', c')))));
          == {AddTransitive(a', b', c');
          Suc(Suc(Suc(Add(Add(a',b'), c'))));
          == // def. Add
          Suc(Suc(Add(Add(a', b'), Suc(c'))));
          == {SucAdd(Add(a', b'), Suc(c'));
          Suc(Add(Suc(Add(a', b')), Suc(c')));
          == {SucAdd(a', b');
          Suc(Add(Add(Suc(a'), b'), Suc(c')));
          == {SucAdd(Add(Suc(a'), b'), Suc(c'));
          Add(Suc(Add(Suc(a'), b')), Suc(c'));
          == // def. Add
          Add(Add(Suc(a'), Suc(b')), Suc(c'));
          ==
          Add(Add(a,b), c);
        }

}

lemma AddCommutative(a: Unary, b: Unary)
  ensures Add(a, b) == Add(b, a)
{
  match b
  case Zero => 
    calc{
      Add(a, b);
      ==
      Add(a, Zero);
      == // def. Add
      a;
      == {AddZero(a);
      Add(Zero, a);
      ==
      Add(b, a);
    }
  case Suc(b') =>
    calc{
      Add(a, b);
      ==
      Add(a, Suc(b'));
      == // def. Add
      Suc(Add(a, b'));
      == {AddCommutative(a, b');
      Suc(Add(b', a));
      == {SucAdd(b', a);
      Add(Suc(b'), a);
      ==
      Add(b, a);
    }
}



method Main() {
  var U3 := Suc(Suc(Suc(Zero)));
  var U7 := Suc(Suc(Suc(Suc(U3))));
  var d, m := IterativeDivMod(U7, U3);
  print "Just as 7 divided by 3 is 2 with a remainder of 1, IterativeDivMod(", U7, ", ", U3, ") is ", d, " with a remainder of ", m;
}

// Kept File 14:
// filename: dafny-synthesis_task_id_106_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_106_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
{}
// Kept File 15:
// filename: Clover_find_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_find_no_hints.dfy
// keepToss: KEEP
// duplicateGroup: nan

method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
{}

// Tossed File 1:
// filename: Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec_no_hints.dfy
// keepToss: TOSS
// duplicateGroup: 4.0
// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:   Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//   dafny H2-skeleton.dfy
// or
//   compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;

{}

method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
{}

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.
method Test( a: seq<real>, x: real )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q];
{}



// Tossed File 2:
// filename: Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise4_Find_Max_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise4_Find_Max_no_hints.dfy
// keepToss: TOSS
// duplicateGroup: 5.0
method findMax(a:array<int>) returns (pos:int, maxVal: int)
  requires a.Length > 0;
  requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal;
  ensures exists i :: 0 <= i < a.Length &&  a[i] == maxVal;
  ensures 0 <= pos < a.Length
  ensures a[pos] == maxVal;
{}



// Tossed File 3:
// filename: dafny-synthesis_task_id_618_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_618_no_hints.dfy
// keepToss: TOSS
// duplicateGroup: 7.0
method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{}



// Tossed File 4:
// filename: HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Two Sum_two_sum_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Two Sum_two_sum_no_hints.dfy
// keepToss: TOSS
// duplicateGroup: 0.0
method twoSum(nums: array<int>, target: int) returns (index1: int, index2: int)
    requires 2 <= nums.Length
    requires exists i, j :: (0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures index1 != index2
    ensures 0 <= index1 < nums.Length
    ensures 0 <= index2 < nums.Length
    ensures nums[index1] + nums[index2] == target
{}


// Tossed File 5:
// filename: dafny-synthesis_task_id_3_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_3_no_hints.dfy
// keepToss: TOSS
// duplicateGroup: 1.0
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
{}


// Tossed File 6:
// filename: dafny-workout_tmp_tmp0abkw6f8_starter_ex12_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-workout_tmp_tmp0abkw6f8_starter_ex12_no_hints.dfy
// keepToss: TOSS
// duplicateGroup: 2.0

method FindMax(a: array<int>) returns (max_idx: nat)
	requires a.Length > 0
	ensures 0 <= max_idx < a.Length
	ensures forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
{}

method Main()
{}

// Tossed File 7:
// filename: Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_BinarySearch_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_BinarySearch_no_hints.dfy
// keepToss: TOSS
// duplicateGroup: 3.0
method BinarySearch(a: array<int>, key: int) returns (n: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n <= a.Length
    ensures forall i :: 0 <= i < n ==> a[i] < key
    ensures forall i :: n <= i < a.Length ==> key <= a[i]
{}




