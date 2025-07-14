
// predicate recSorted(s : string) decreases s
// {}

// predicate forallSorted (s : string)
// {}

// lemma forallEQrec(a:string)
// ensures forallSorted(a) == recSorted(a) {
 
// }
        
// //  method Main() {}

 
// /*omitted*/
/*  verify one of ensures r == forallSorted(a) OR 
                  ensures r == recSorted(a) 
        Only one might work */
// method whileSorted(a:string) returns (r : bool) 
// ensures r == forallSorted(a) // ONEOF
// //ensures r == recSorted(a)    // ONEOF

// {}

// lemma SortedSumForall(a:string,b:string)
//   requires forallSorted(a)
//   requires forallSorted(b)
//   ensures forallSorted(a + b) 
//   requires (|a| >0 && |b| >0 ) ==> a[|a|-1] <= b[0]
//  {

//  }

// /*omitted*/
// // Prove using forallSorted not recursivly using SortedSumRec
//  lemma SortedSumRec(a:string,b:string)
//   requires recSorted(a)
//   requires recSorted(b)
//   requires |a| > 0 && |b| > 0
//   requires a[|a|-1] <= b[0]
//   ensures recSorted(a + b)
//   {}

//     predicate recSorted(s : string) decreases s
//  /*omitted*/
//  // Prove using Induction not using forallEQrec
//  lemma SortedSumInduction(a:string,b:string)
//   requires recSorted(a)
//   requires recSorted(b)
//   requires |a| > 0 && |b| > 0
//   requires a[|a|-1] <= b[0]
//   ensures recSorted(a + b)
//   {}

// lemma VowelsLemma(s : string, t : string) 
//   ensures vowels(s + t) == vowels(s) + vowels(t) 
//   //verify this lemma - https://youtu.be/LFLD48go9os
// {}

//so far straightwawrd
// function vowels(s : string) : (r : nat)
//  {}


// //see, this one is soooo EASY!!!
// function vowelsF(s : string) : nat {}

// lemma VowelsLemmaF(s : string, t : string) 
//   ensures vowelsF(s + t) == vowelsF(s) + vowelsF(t) 
// {}

// // method Main() {}


// class KlingonCalendar {}

// lemma VowelsLemma(s : string, t : string) 
//   ensures vowels(s + t) == vowels(s) + vowels(t) 
//   //verify this lemma - https://youtu.be/LFLD48go9os
// {
// }

// //so far straightwawrd
// function vowels(s : string) : (r : nat)
//  {}


// //see, this one is soooo EASY!!!
// function vowelsF(s : string) : nat {}

// lemma VowelsLemmaF(s : string, t : string) 
//   ensures vowelsF(s + t) == vowelsF(s) + vowelsF(t) 
// {}

// class Stack {}

// method VerifyStack(s : Stack, i : int, j : int)
//  modifies s, s.values
//  requires 0 <= s.size < (s.values.Length - 2)
//  requires s.values.Length == s.capacity
//  requires s.size == 0
//   {}


// datatype StackModel = Empty | Push(value : int, prev : StackModel)

// class Stack {}

// method StackModelOK(s : Stack, i : int, j : int)
//  requires s.values.Length == s.capacity
//  modifies s, s.values
//  requires s.size == 0
//  requires s.capacity > 2
//   {}


// datatype StackModel = Empty | Push(value : int, prev : StackModel)

// class Stack {}





// method StackOK(s : Stack, i : int, j : int)
//  requires s.Valid()
//  requires 0 <= s.size < (s.capacity - 2)
//  requires s.values.Length == s.capacity

//  requires s.size == 0
//  requires s.capacity > 2
//  modifies s.Repr
//   {}

        

