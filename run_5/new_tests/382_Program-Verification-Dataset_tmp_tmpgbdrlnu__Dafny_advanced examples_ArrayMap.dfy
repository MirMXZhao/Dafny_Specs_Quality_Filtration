method ArrayMap<A>(f: int -> A, a: array<A>)
  requires a != null
  requires forall j :: 0 <= j < a.Length ==> f.requires(j)
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j)
  modifies a
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j)
{}

////////TESTS////////

method TestArrayMap1() {
  var a := new int[3];
  a[0] := 10; a[1] := 20; a[2] := 30;
  ArrayMap(x => x * 2, a);
  assert a[0] == 0;
  assert a[1] == 2;
  assert a[2] == 4;
}

method TestArrayMap2() {
  var a := new int[2];
  a[0] := 5; a[1] := 15;
  ArrayMap(x => x + 1, a);
  assert a[0] == 1;
  assert a[1] == 2;
}
