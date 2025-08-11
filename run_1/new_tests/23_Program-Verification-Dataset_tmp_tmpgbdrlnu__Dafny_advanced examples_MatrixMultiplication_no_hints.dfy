function RowColumnProduct(m1: array2<int>, m2: array2<int>, row: nat, column: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
{}

function RowColumnProductFrom(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && k <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
{}

method multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
    requires m1 != null && m2 != null
    requires m1.Length1 == m2.Length0
    ensures m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
    ensures forall i, j | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ::
        m3[i, j] == RowColumnProduct(m1, m2, i, j)
{}

////////TESTS////////

method TestMultiply1() {
  var m1 := new int[2, 3];
  m1[0, 0] := 1; m1[0, 1] := 2; m1[0, 2] := 3;
  m1[1, 0] := 4; m1[1, 1] := 5; m1[1, 2] := 6;
  
  var m2 := new int[3, 2];
  m2[0, 0] := 7; m2[0, 1] := 8;
  m2[1, 0] := 9; m2[1, 1] := 10;
  m2[2, 0] := 11; m2[2, 1] := 12;
  
  var m3 := multiply(m1, m2);
  assert m3.Length0 == 2;
  assert m3.Length1 == 2;
}

method TestMultiply2() {
  var m1 := new int[1, 2];
  m1[0, 0] := 2; m1[0, 1] := 3;
  
  var m2 := new int[2, 1];
  m2[0, 0] := 4;
  m2[1, 0] := 5;
  
  var m3 := multiply(m1, m2);
  assert m3.Length0 == 1;
  assert m3.Length1 == 1;
}
