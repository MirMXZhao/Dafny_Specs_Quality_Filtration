/*
  A simple state machine modeling checking out and returning books in a library.
*/

// Status will track where one book is
datatype Status = Shelf | Patron(name: string)
datatype Book = Book(title: string)

// The state of the whole library is just the status of every book owned by the
// library.
datatype Variables = Variables(library: map<Book, Status>)
{
  // New syntax (member function): the curly braces below the datatype introduce
  // a set of _member functions_, which can be called as v.f(), just like Java,
  // C++, or Rust methods. Just like in Java or C++, the body can use the `this`
  // keyword to refer to an implicit argument of type Variables.
  ghost predicate WellFormed()
  {}
}

ghost predicate Init(v: Variables)
{}

// The transitions of the library state machine.

datatype Step = Checkout(b: Book, to: string) | Return(b: Book)

ghost predicate CheckoutStep(v: Variables, v': Variables, step: Step)
  requires step.Checkout?
{}

ghost predicate ReturnStep(v: Variables, v': Variables, step: Step)
  requires step.Return?
{}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{}

ghost predicate Next(v: Variables, v': Variables)
{}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

/*
In this lemma we'll write a concrete sequence of states which forms a (short)
execution of this state machine, and prove that it really is an execution.

This can be a good sanity check on the definitions (for example, to make sure
that it's at least possible to take every transition).
*/
lemma ExampleExec() {}

