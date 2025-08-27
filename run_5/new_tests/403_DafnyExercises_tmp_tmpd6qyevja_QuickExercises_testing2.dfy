predicate recSorted(s : string) decreases s
{    
       if (|s| <=1) then true else if(s[0] > s[1]) then false else recSorted(s[1..])
}

predicate forallSorted (s : string)
{ 
    forall x,y::0<x<y<|s|==>s[x]<s[y]
}

lemma forallEQrec(a:string)
ensures forallSorted(a) == recSorted(a) {
 
}

method whileSorted(a:string) returns (r : bool) 
ensures r == forallSorted(a)

{}

lemma SortedSumForall(a:string,b:string)
  requires forallSorted(a)
  requires forallSorted(b)
  ensures forallSorted(a + b) 
  requires (|a| >0 && |b| >0 ) ==> a[|a|-1] <= b[0]
 {

 }

 lemma SortedSumRec(a:string,b:string)
  requires recSorted(a)
  requires recSorted(b)
  requires |a| > 0 && |b| > 0
  requires a[|a|-1] <= b[0]
  ensures recSorted(a + b)
  {}

 lemma SortedSumInduction(a:string,b:string)
  requires recSorted(a)
  requires recSorted(b)
  requires |a| > 0 && |b| > 0
  requires a[|a|-1] <= b[0]
  ensures recSorted(a + b)
  {}

lemma VowelsLemma(s : string, t : string) 
  ensures vowels(s + t) == vowels(s) + vowels(t) 
{}

function vowels(s : string) : (r : nat)
 {}

function vowelsF(s : string) : nat {}

lemma VowelsLemmaF(s : string, t : string) 
  ensures vowelsF(s + t) == vowelsF(s) + vowelsF(t) 
{}

class KlingonCalendar {}

function vowels(s : string) : (r : nat)
 {}

function vowelsF(s : string) : nat {}

lemma VowelsLemmaF(s : string, t : string) 
  ensures vowelsF(s + t) == vowelsF(s) + vowelsF(t) 
{}

class Stack {}

method VerifyStack(s : Stack, i : int, j : int)
 modifies s, s.values
 requires 0 <= s.size < (s.values.Length - 2)
 requires s.values.Length == s.capacity
 requires s.size == 0
  {}

datatype StackModel = Empty | Push(value : int, prev : StackModel)

class Stack {}

method StackModelOK(s : Stack, i : int, j : int)
 requires s.values.Length == s.capacity
 modifies s, s.values
 requires s.size == 0
 requires s.capacity > 2
  {}

datatype StackModel = Empty | Push(value : int, prev : StackModel)

class Stack {}

method StackOK(s : Stack, i : int, j : int)
 requires s.Valid()
 requires 0 <= s.size < (s.capacity - 2)
 requires s.values.Length == s.capacity
 requires s.size == 0
 requires s.capacity > 2
 modifies s.Repr
  {}

////////TESTS////////

method TestwhileSorted1() {
  var a := "abc";
  var r := whileSorted(a);
  assert r == true;
}

method TestwhileSorted2() {
  var a := "bac";
  var r := whileSorted(a);
  assert r == false;
}

method TestVerifyStack1() {
  var s := new Stack;
  assume s.values != null && s.values.Length == 10;
  assume s.capacity == 10;
  assume s.size == 0;
  VerifyStack(s, 5, 3);
}

method TestVerifyStack2() {
  var s := new Stack;
  assume s.values != null && s.values.Length == 5;
  assume s.capacity == 5;
  assume s.size == 0;
  VerifyStack(s, 1, 2);
}

method TestStackModelOK1() {
  var s := new Stack;
  assume s.values != null && s.values.Length == 5;
  assume s.capacity == 5;
  assume s.size == 0;
  StackModelOK(s, 10, 20);
}

method TestStackModelOK2() {
  var s := new Stack;
  assume s.values != null && s.values.Length == 10;
  assume s.capacity == 10;
  assume s.size == 0;
  StackModelOK(s, 7, 8);
}

method TestStackOK1() {
  var s := new Stack;
  assume s.Valid();
  assume s.size == 0;
  assume s.capacity == 5;
  assume s.values.Length == 5;
  assume s.Repr != null;
  StackOK(s, 1, 2);
}

method TestStackOK2() {
  var s := new Stack;
  assume s.Valid();
  assume s.size == 0;
  assume s.capacity == 10;
  assume s.values.Length == 10;
  assume s.Repr != null;
  StackOK(s, 3, 4);
}
