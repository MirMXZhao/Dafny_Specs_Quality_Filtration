codatatype Stream<T> = SNil | SCons(head: T, tail: Stream<T>)

function Up(n: int): Stream<int>
{}

function FivesUp(n: int): Stream<int>
  decreases 4 - (n-1) % 5;
{}

copredicate Pos(s: Stream<int>)
{
  match s
  case SNil => true
  case SCons(x, rest) => x > 0 && Pos(rest)
}

function SAppend(xs: Stream, ys: Stream): Stream
{}

lemma {:induction false} SAppendIsAssociativeK(k:nat, a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c));
  decreases k;
{}

lemma SAppendIsAssociative(a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
{}

colemma {:induction false} SAppendIsAssociativeC(a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
{}

colemma SAppendIsAssociative_Auto(a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
{
}

colemma {:induction false} UpPos(n:int)
  requires n > 0;
  ensures Pos(Up(n));
{
  UpPos(n+1);
}

colemma UpPos_Auto(n:int)
  requires n > 0;
  ensures Pos(Up(n));
{
}

colemma {:induction false} FivesUpPos(n:int)
  requires n > 0;
  ensures Pos(FivesUp(n));
  decreases 4 - (n-1) % 5;
{}

colemma FivesUpPos_Auto(n:int)
  requires n > 0;
  ensures Pos(FivesUp(n));
  decreases 4 - (n-1) % 5;
{
}