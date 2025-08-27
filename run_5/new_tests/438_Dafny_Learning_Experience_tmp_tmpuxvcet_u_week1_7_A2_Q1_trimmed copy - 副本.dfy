ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{}

method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
{}

method FooPreCompute(a:array<int>,b:array<int>)
    requires a.Length == b.Length
    modifies b
{}

method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
{}

method PreCompute(a:array<int>,b:array<int>)returns(p:nat)
    requires a.Length == b.Length 
    modifies b
    ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
    forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..])

{}

method Evens(a:array<int>) returns (c:array2<int>)
{}

method Mult(x:int, y:int) returns (r:int)
    requires x>= 0 && y>=0
    decreases x
    ensures r == x*y
{}

////////TESTS////////

method TestFooCount1() {
  var a := [1, 2, 3, 4];
  var b := new int[4];
  var p := FooCount(2, a, b);
  assert p == Count(2, a);
}

method TestFooCount2() {
  var a := [5, 6, 7];
  var b := new int[3];
  var p := FooCount(0, a, b);
  assert p == Count(0, a);
}

method TestFooPreCompute1() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  var b := new int[3];
  FooPreCompute(a, b);
}

method TestFooPreCompute2() {
  var a := new int[2];
  a[0], a[1] := 5, 10;
  var b := new int[2];
  FooPreCompute(a, b);
}

method TestComputeCount1() {
  var a := [1, 2, 3];
  var b := new int[3];
  var p := ComputeCount(3, a, b);
  assert p == Count(3, a);
}

method TestComputeCount2() {
  var a := [4, 5];
  var b := new int[2];
  var p := ComputeCount(1, a, b);
  assert p == Count(1, a);
}

method TestPreCompute1() {
  var a := new int[2];
  a[0], a[1] := 1, 2;
  var b := new int[2];
  var p := PreCompute(a, b);
  assert p == Count(b.Length, a[..]);
}

method TestPreCompute2() {
  var a := new int[3];
  a[0], a[1], a[2] := 3, 4, 5;
  var b := new int[3];
  var p := PreCompute(a, b);
  assert p == Count(b.Length, a[..]);
}

method TestEvens1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 2, 4, 6, 8;
  var c := Evens(a);
}

method TestEvens2() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 3, 5;
  var c := Evens(a);
}

method TestMult1() {
  var r := Mult(3, 4);
  assert r == 12;
}

method TestMult2() {
  var r := Mult(0, 5);
  assert r == 0;
}
