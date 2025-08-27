method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{}

////////TESTS////////

method TestIsSublist1() {
  var sub := [2, 3];
  var main := [1, 2, 3, 4];
  var result := IsSublist(sub, main);
  assert result == true;
}

method TestIsSublist2() {
  var sub := [2, 4];
  var main := [1, 2, 3, 4];
  var result := IsSublist(sub, main);
  assert result == false;
}
