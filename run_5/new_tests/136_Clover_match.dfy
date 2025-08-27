method Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{}

////////TESTS////////

method TestMatch1() {
  var s := "abc";
  var p := "a?c";
  var b := Match(s, p);
  assert b == true;
}

method TestMatch2() {
  var s := "abc";
  var p := "a?d";
  var b := Match(s, p);
  assert b == false;
}
