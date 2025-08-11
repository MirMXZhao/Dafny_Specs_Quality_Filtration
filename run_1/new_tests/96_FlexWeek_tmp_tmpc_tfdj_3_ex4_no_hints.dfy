method join(a:array<int>,b:array<int>) returns (c:array<int>)
ensures a[..] + b[..] == c[..]
ensures multiset(a[..] + b[..]) == multiset(c[..])
ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
ensures a.Length+b.Length == c.Length
ensures forall i :: 0<=i<a.Length ==> c[i] == a[i]
ensures forall i_2,j_2::
    a.Length <= i_2 < c.Length &&
    0<=j_2< b.Length && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2]
{}

////////TESTS////////

method TestJoin1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var b := new int[2];
  b[0] := 4; b[1] := 5;
  var c := join(a, b);
  assert c[..] == [1, 2, 3, 4, 5];
}

method TestJoin2() {
  var a := new int[0];
  var b := new int[4];
  b[0] := 7; b[1] := 8; b[2] := 9; b[3] := 10;
  var c := join(a, b);
  assert c[..] == [7, 8, 9, 10];
}
