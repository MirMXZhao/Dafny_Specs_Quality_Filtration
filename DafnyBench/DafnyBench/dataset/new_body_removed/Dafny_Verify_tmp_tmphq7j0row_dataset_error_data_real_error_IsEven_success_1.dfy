function even(n: int): bool
  requires n >= 0
{}

method is_even(n: int) returns (r: bool)
  requires n >= 0;
  ensures r <==> even(n);
{}
