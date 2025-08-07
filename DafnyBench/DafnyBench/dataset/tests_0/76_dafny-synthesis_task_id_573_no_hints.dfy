method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{}

ghost function SetProduct(s : set<int>) : int
{}

// This is necessary because, when we add one element, we need to make sure
// that the product of the new set, as a whole, is the same as the product
// of the old set times the new element.
lemma SetProductLemma(s: set <int>, x: int) 
 requires x in s
 ensures SetProduct(s - {x}) * x == SetProduct(s)
{}

////////TESTS////////

method TestUniqueProduct1() {
  var arr := new int[4];
  arr[0] := 2;
  arr[1] := 3;
  arr[2] := 2;
  arr[3] := 5;
  var product := UniqueProduct(arr);
  assert product == 30;
}

method TestUniqueProduct2() {
  var arr := new int[3];
  arr[0] := 1;
  arr[1] := 1;
  arr[2] := 1;
  var product := UniqueProduct(arr);
  assert product == 1;
}

method TestUniqueProduct3() {
  var arr := new int[0];
  var product := UniqueProduct(arr);
  assert product == 1;
}
