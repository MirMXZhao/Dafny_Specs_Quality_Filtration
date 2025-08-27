/*
  A simple state machine modeling checking out and returning books in a library.
*/

// Status will track where one book is
datatype Status = Shelf | Patron(name: string)
datatype Book = Book(title: string)

// The state of the whole library is just the status of every book owned by the
// library.
datatype Variables = Variables(library: map<Book, Status>)
{}

ghost predicate Init(v: Variables)
{
  && v.WellFormed()
  && forall b :: b in v.library ==> v.library[b].Shelf?
}

// The transitions of the library state machine.

datatype Step = Checkout(b: Book, to: string) | Return(b: Book)

ghost predicate CheckoutStep(v: Variables, v': Variables, step: Step)
  requires step.Checkout?
{
  && v.WellFormed()
  && step.b in v.library
  && v.library[step.b].Shelf?
     // New syntax (datatype update): here we define the new Variables from the old
     // one by updating one field: v.(library := ...). This is much like a sequence
     // update. In fact, we also introduce a map update `v.library[step.b := ...]`
     // which works in pretty much the same way.
  && v' == v.(library := v.library[step.b := Patron(step.to)])
}

ghost predicate ReturnStep(v: Variables, v': Variables, step: Step)
  requires step.Return?
{
  && v.WellFormed()
  && step.b in v.library
  && v.library[step.b].Patron?
  && v' == v.(library := v.library[step.b := Shelf])
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case Checkout(_, _) => CheckoutStep(v, v', step)
    case Return(_) => ReturnStep(v, v', step)
  }
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

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

