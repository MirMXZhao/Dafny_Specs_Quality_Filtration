method insert(line:array<char>, l:int, nl:array<char>, p:int, at:int)
  requires 0 <= l+p <= line.Length
  requires 0 <= p <= nl.Length
  requires 0 <= at <= l
  modifies line
  ensures forall i :: (0<=i<p) ==> line[at+i] == nl[i]
  ensures forall i :: (0<=i<at) ==> line[i] == old(line[i])
  ensures forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
{}

method TestInsert1() {
  var line := new char[10];
  line[0] := 'a'; line[1] := 'b'; line[2] := 'c'; line[3] := 'd'; line[4] := 'e';
  var nl := new char[3];
  nl[0] := 'x'; nl[1] := 'y'; nl[2] := 'z';
  insert(line, 5, nl, 3, 2);
  assert line[0] == 'a';
  assert line[1] == 'b';
  assert line[2] == 'x';
  assert line[3] == 'y';
  assert line[4] == 'z';
  assert line[5] == 'c';
  assert line[6] == 'd';
  assert line[7] == 'e';
}

method TestInsert2() {
  var line := new char[8];
  line[0] := 'h'; line[1] := 'e'; line[2] := 'l'; line[3] := 'o';
  var nl := new char[2];
  nl[0] := 'l'; nl[1] := 'l';
  insert(line, 4, nl, 2, 0);
  assert line[0] == 'l';
  assert line[1] == 'l';
  assert line[2] == 'h';
  assert line[3] == 'e';
  assert line[4] == 'l';
  assert line[5] == 'o';
}
