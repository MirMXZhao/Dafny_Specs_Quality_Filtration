datatype Status = Shelf | Patron(name: string)
datatype Book = Book(title: string)

datatype Variables = Variables(library: map<Book, Status>)
{}

ghost predicate Init(v: Variables)
{
  && v.WellFormed()
  && forall b :: b in v.library ==> v.library[b].Shelf?
}

datatype Step = Checkout(b: Book, to: string) | Return(b: Book)

ghost predicate CheckoutStep(v: Variables, v': Variables, step: Step)
  requires step.Checkout?
{
  && v.WellFormed()
  && step.b in v.library
  && v.library[step.b].Shelf?
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