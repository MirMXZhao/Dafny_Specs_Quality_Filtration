method RemoveElement(s: array<int>, k: int) returns (v: array<int>)
    requires 0 <= k < s.Length
    ensures v.Length == s.Length - 1
    ensures forall i :: 0 <= i < k ==> v[i] == s[i]
    ensures forall i :: k <= i < v.Length ==> v[i] == s[i + 1]
{}

////////TESTS////////

method TestRemoveElement1() {
  var s := new int[4];
  s[0] := 10; s[1] := 20; s[2] := 30; s[3] := 40;
  var v := RemoveElement(s, 1);
  assert v.Length == 3;
  assert v[0] == 10;
  assert v[1] == 30;
  assert v[2] == 40;
}

method TestRemoveElement2() {
  var s := new int[3];
  s[0] := 5; s[1] := 15; s[2] := 25;
  var v := RemoveElement(s, 0);
  assert v.Length == 2;
  assert v[0] == 15;
  assert v[1] == 25;
}
