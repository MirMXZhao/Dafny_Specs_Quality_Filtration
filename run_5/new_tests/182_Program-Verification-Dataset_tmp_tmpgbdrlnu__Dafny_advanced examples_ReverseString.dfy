predicate reversed (arr : array<char>, outarr: array<char>)
requires arr != null && outarr != null
requires arr.Length == outarr.Length
reads arr, outarr
{}

method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr != null && arr.Length > 0
ensures outarr != null && arr.Length == outarr.Length && reversed(arr,outarr)
{}

////////TESTS////////

method TestYarra1() {
  var arr := new char[3];
  arr[0] := 'a';
  arr[1] := 'b';
  arr[2] := 'c';
  var outarr := yarra(arr);
  assert outarr[0] == 'c';
  assert outarr[1] == 'b';
  assert outarr[2] == 'a';
}

method TestYarra2() {
  var arr := new char[1];
  arr[0] := 'x';
  var outarr := yarra(arr);
  assert outarr[0] == 'x';
}
