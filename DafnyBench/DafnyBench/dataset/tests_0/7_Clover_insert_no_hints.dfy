method insert(line:array<char>, l:int, nl:array<char>, p:int, at:int)
  requires 0 <= l+p <= line.Length
  requires 0 <= p <= nl.Length
  requires 0 <= at <= l
  modifies line
  ensures forall i :: (0<=i<p) ==> line[at+i] == nl[i]
  ensures forall i :: (0<=i<at) ==> line[i] == old(line[i])
  ensures forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
{}

////////TESTS////////

method testinsert1() {
  var line := new char[10];
  line[0] := 'a';
  line[1] := 'b';
  line[2] := 'c';
  line[3] := 'd';
  var nl := new char[2];
  nl[0] := 'x';
  nl[1] := 'y';
  insert(line, 4, nl, 2, 2);
  assert line[0] == 'a';
  assert line[1] == 'b';
  assert line[2] == 'x';
  assert line[3] == 'y';
  assert line[4] == 'c';
  assert line[5] == 'd';
}

method testinsert2() {
  var line := new char[5];
  line[0] := 'h';
  line[1] := 'e';
  line[2] := 'l';
  var nl := new char[3];
  nl[0] := 'X';
  nl[1] := 'Y';
  nl[2] := 'Z';
  insert(line, 3, nl, 1, 0);
  assert line[0] == 'X';
  assert line[1] == 'h';
  assert line[2] == 'e';
  assert line[3] == 'l';
}

method testinsert3() {
  var line := new char[6];
  line[0] := 'a';
  line[1] := 'b';
  line[2] := 'c';
  var nl := new char[2];
  nl[0] := 'z';
  nl[1] := 'w';
  insert(line, 3, nl, 2, 3);
  assert line[0] == 'a';
  assert line[1] == 'b';
  assert line[2] == 'c';
  assert line[3] == 'z';
  assert line[4] == 'w';
}
