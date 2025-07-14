method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{}
 
method MaxTest() {}

function max(a: int, b: int): int
{}

method maxTest() {
}
