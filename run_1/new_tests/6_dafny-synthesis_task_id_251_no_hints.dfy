method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
    {}

////////TESTS////////

method TestInsertBeforeEach1() {
  var s := ["a", "b", "c"];
  var x := "x";
  var v := InsertBeforeEach(s, x);
  assert v == ["x", "a", "x", "b", "x", "c"];
}

method TestInsertBeforeEach2() {
  var s := ["hello"];
  var x := "world";
  var v := InsertBeforeEach(s, x);
  assert v == ["world", "hello"];
}
