method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])  
{}
 
predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

////////TESTS////////

method testpartitionOddEven1() {
  var a := new nat[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  partitionOddEven(a);
  assert multiset(a[..]) == multiset([1, 2, 3, 4]);
  assert ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]);
}

method testpartitionOddEven2() {
  var a := new nat[3];
  a[0] := 6; a[1] := 7; a[2] := 8;
  partitionOddEven(a);
  assert multiset(a[..]) == multiset([6, 7, 8]);
  assert ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]);
}

method testpartitionOddEven3() {
  var a := new nat[0];
  partitionOddEven(a);
  assert multiset(a[..]) == multiset([]);
  assert ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]);
}

method testodd1() {
  var result := odd(5);
  assert result == true;
}

method testodd2() {
  var result := odd(4);
  assert result == false;
}

method testeven1() {
  var result := even(6);
  assert result == true;
}

method testeven2() {
  var result := even(7);
  assert result == false;
}
