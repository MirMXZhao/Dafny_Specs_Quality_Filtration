method sort(A: array<int>, n: int)
modifies A; requires n==A.Length;
requires n>=0;            
ensures forall i,j:: 0<=i<=j<n ==> A[i]<=A[j];

{}