method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
    {}

////////TESTS////////

method TestInsertBeforeEach1() {
  var s := ["a", "b", "c"];
  var x := "X";
  var v := InsertBeforeEach(s, x);
  assert v == ["X", "a", "X", "b", "X", "c"];
}

method TestInsertBeforeEach2() {
  var s := ["hello"];
  var x := "start";
  var v := InsertBeforeEach(s, x);
  assert v == ["start", "hello"];
}
