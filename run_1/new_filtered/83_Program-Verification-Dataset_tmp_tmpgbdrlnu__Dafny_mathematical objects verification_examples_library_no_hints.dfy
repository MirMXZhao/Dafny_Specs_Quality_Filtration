datatype Status = Shelf | Patron(name: string)
datatype Book = Book(title: string)

datatype Variables = Variables(library: map<Book, Status>)
{
  ghost predicate WellFormed()
  {}
}

ghost predicate Init(v: Variables)
{}

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

lemma ExampleExec() {}