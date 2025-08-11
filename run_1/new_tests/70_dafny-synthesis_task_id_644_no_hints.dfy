method Reverse(a: array<int>)
	modifies a;
	ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
{}

method ReverseUptoK(s: array<int>, k: int)
    modifies s
    requires 2 <= k <= s.Length
    ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
    ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
{}

////////TESTS////////

method TestReverse1() {
  var a := new int[4] [1, 2, 3, 4];
  Reverse(a);
  assert a[0] == 4 && a[1] == 3 && a[2] == 2 && a[3] == 1;
}

method TestReverse2() {
  var a := new int[3] [5, 10, 15];
  Reverse(a);
  assert a[0] == 15 && a[1] == 10 && a[2] == 5;
}

method TestReverseUptoK1() {
  var s := new int[5] [1, 2, 3, 4, 5];
  ReverseUptoK(s, 3);
  assert s[0] == 3 && s[1] == 2 && s[2] == 1 && s[3] == 4 && s[4] == 5;
}

method TestReverseUptoK2() {
  var s := new int[4] [10, 20, 30, 40];
  ReverseUptoK(s, 2);
  assert s[0] == 20 && s[1] == 10 && s[2] == 30 && s[3] == 40;
}
