function to_seq<T>(a: array<T>, i: int) : (res: seq<T>)
requires 0 <= i <= a.Length
ensures res == a[i..]
reads a
decreases a.Length-i
{}

////////TESTS////////

method Testto_seq1() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 3;
  a[2] := 8;
  a[3] := 1;
  var res := to_seq(a, 2);
  assert res == [8, 1];
}

method Testto_seq2() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  var res := to_seq(a, 0);
  assert res == [10, 20, 30];
}
