module OneSpec {
    datatype Variables = Variables(value: int)

    predicate Init(v: Variables)
    {}

    predicate IncrementOp(v: Variables, v': Variables)
    {}

    predicate DecrementOp(v: Variables, v': Variables)
    {}

    datatype Step = 
        | IncrementStep()
        | DecrementStep()

    predicate NextStep(v: Variables, v': Variables, step: Step)
    {}

    predicate Next(v: Variables, v': Variables)
    {}
}

module OneProtocol {
    datatype Variables = Variables(value: int)

    predicate Init(v: Variables)
    {}

    predicate IncrementOp(v: Variables, v': Variables)
    {}

    predicate DecrementOp(v: Variables, v': Variables)
    {}

    datatype Step = 
        | IncrementStep()
        | DecrementStep()

    predicate NextStep(v: Variables, v': Variables, step: Step)
    {}

    predicate Next(v: Variables, v': Variables)
    {}
}

module RefinementProof {
    import OneSpec
    import opened OneProtocol

    function Abstraction(v: Variables) : OneSpec.Variables {}

    lemma RefinementInit(v: Variables)
        requires Init(v)
        ensures OneSpec.Init(Abstraction(v))
    {

    }

    lemma RefinementNext(v: Variables, v': Variables)
        requires Next(v, v')
        ensures OneSpec.Next(Abstraction(v), Abstraction(v'))
    {}
}
