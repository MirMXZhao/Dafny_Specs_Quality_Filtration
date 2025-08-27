function M1(f:map<int, bool>, i:int):bool

function M2(f:map<int, bool>, i:int):bool
{}

lemma L(f:map<int, bool>, i:int)
    requires i in f;
    requires M2(f, i);
    requires forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
{
    assert f[i];
}