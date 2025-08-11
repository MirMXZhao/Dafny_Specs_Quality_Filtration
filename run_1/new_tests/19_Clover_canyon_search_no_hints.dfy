method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{}

////////TESTS////////

method TestCanyonSearch1() {
  var a := new int[3] [1, 3, 5];
  var b := new int[2] [2, 4];
  var d := CanyonSearch(a, b);
  assert d == 1;
}

method TestCanyonSearch2() {
  var a := new int[2] [10, 20];
  var b := new int[3] [1, 5, 15];
  var d := CanyonSearch(a, b);
  assert d == 5;
}
