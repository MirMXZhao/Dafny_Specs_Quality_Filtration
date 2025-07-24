/*
You are climbing a staircase. It takes n steps to reach the top.

Each time you can either climb 1 or 2 steps. In how many distinct ways can you climb to the top?
function climbStairs(n: number): number {};
*/

datatype Steps = One | Two

function stepSum(xs: seq<Steps>): nat {}

ghost predicate stepEndsAt(xs: seq<Steps>, n: nat) {}
ghost predicate allEndAtN(ss: set<seq<Steps> >, n: nat) {}

lemma stepBaseZero() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 0) && |ss| == 0
{
}
lemma stepBaseOne() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 1) && |ss| == 1
{
}

lemma stepBaseTwo() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 2) && |ss| == 2
{
}

ghost function plusOne(x: seq<Steps>): seq<Steps> {
    [One]+x
}

ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
    ensures addOne(ss) == set x | x in ss :: plusOne(x)
{}

lemma SeqsNotEqualImplication<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures (exists i: nat :: i < |xs| && i <|ys| && xs[i] != ys[i]) || |xs| < |ys| || |ys| < |xs|
{}

lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures [someT]+xs != [someT]+ys
{}

lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusOne(x) !in addOne(ss)
{}

lemma addOneSize(ss: set<seq<Steps>>)
    ensures |addOne(ss)| == |ss|
{}

lemma addOneSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addOne(ss), sum+1)
{

}

lemma endAtNPlus(ss: set<seq<Steps>>, sz: set<seq<Steps>>, sum: nat)
    requires allEndAtN(ss, sum)
    requires allEndAtN(sz, sum)
    ensures allEndAtN(ss+sz, sum)
{

}

ghost function plusTwo(x: seq<Steps>): seq<Steps> {
    [Two]+x
}

ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
    ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{}

lemma plusTwoNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusTwo(x) !in addTwo(ss)
{}

lemma addTwoSize(ss: set<seq<Steps>>)
    ensures |addTwo(ss)| == |ss|
{}

lemma addTwoSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addTwo(ss), sum+2)
{

}

lemma setSizeAddition<T>(sx: set<T>, sy: set<T>, sz: set<T>) 
    requires sx !! sy
    requires sz == sx + sy
    ensures |sx + sy| == |sx| + |sy|
    ensures |sz| == |sx| + |sy|
{

}

lemma stepSetsAdd(i: nat, steps: array<nat>) 
    requires i >= 2
    requires steps.Length >= i+1
    requires forall k: nat :: k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
    ensures exists sp : set< seq<Steps> > :: |sp| == steps[i-1] + steps[i-2] && allEndAtN(sp, i)
{}

method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{}


method Test() {}
