


//Method barrier below receives an array and an integer p
//and returns a boolean b which is true if and only if 
//all the positions to the left of p and including also position p contain elements 
//that are strictly smaller than all the elements contained in the positions to the right of p 

//Examples:
// If v=[7,2,5,8] and p=0 or p=1 then the method must return false, 
// but for p=2 the method should return true
//1.Specify the method
//2.Implement an O(v.size()) method
//3.Verify the method

method barrier(v:array<int>,p:int) returns (b:bool)
//Give the precondition
//Give the postcondition
//{}
requires v.Length > 0
requires 0<=p<v.Length
ensures b==forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l]
{}



method TestBarrier1() {
  var v := new int[4];
  v[0] := 7; v[1] := 2; v[2] := 5; v[3] := 8;
  var b := barrier(v, 2);
  assert b == true;
}

method TestBarrier2() {
  var v := new int[4];
  v[0] := 7; v[1] := 2; v[2] := 5; v[3] := 8;
  var b := barrier(v, 1);
  assert b == false;
}
