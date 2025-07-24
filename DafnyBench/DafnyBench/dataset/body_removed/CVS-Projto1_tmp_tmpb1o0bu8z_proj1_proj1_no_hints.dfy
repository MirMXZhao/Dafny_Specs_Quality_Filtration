//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
reads a
requires 0 <= i <= j <= a.Length
{}

//Exercicio 1.b)
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
{}

//Exercicio 1.c)
lemma queryLemma(a:array<int>, i:int, j:int, k:int)
    requires 0 <= i <= k <= j <= a.Length
    ensures  sum(a,i,k) + sum(a,k,j) == sum(a,i,j)
{
}

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
{}

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{}

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{}

function mem<T(==)> (x: T, l:List<T>) : bool
{}

