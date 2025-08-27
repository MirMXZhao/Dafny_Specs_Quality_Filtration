datatype State = State(m:map<int, bool>)

datatype MyDt = MakeA(x: int, bool) | MakeB(s: multiset<int>, t: State)

datatype GenDt<X,Y> = Left(X) | Middle(X,int,Y) | Right(y: Y)

method ChangeGen(g: GenDt)
{}

datatype Recursive<X> = Red | Green(next: Recursive, m: set)

lemma RecLem(r: Recursive) returns (s: Recursive)
  ensures r == s
{}

////////TESTS////////

method TestChangeGen1() {
  var g := Left(42);
  ChangeGen(g);
}

method TestChangeGen2() {
  var g := Right(true);
  ChangeGen(g);
}
