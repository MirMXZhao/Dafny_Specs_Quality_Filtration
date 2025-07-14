// Code taken from the following paper: http://leino.science/papers/krml260.pdf

// Each philosopher's pseudocode:

// repeat forever {}

// control state values; thinking, hungry, eating
// introduce state for each process: use map from processes to values

type Process(==) // {}
datatype CState = Thinking | Hungry | Eating

// provides mutual exclusion
class TicketSystem {
    var ticket: int
    var serving: int
    const P: set<Process>

    var cs: map<Process, CState> // cannot use state variable P as domain for maps => use Process => every conceivable process
    var t: map<Process, int> // ticket number for each philosopher

    // how to know some process p is in domain of map: introduce function which tells whether condition holds or not
    predicate Valid() // function which describes system invariant
        reads this // may depend on values in the class
    {}

    constructor (processes: set<Process>)
        ensures Valid() // postcondition
    {}

    // atomic events to formalize for each process: request, enter, leave
    // model each atomic event by a method

    // atomicity: read or write just once in body
    // method AtomicStep(p: Process)
    //     requires Valid() && p in P && cs[p] == Thinking // Request(p) is only enabled when p is thinking
    //     modifies this
    //     ensures Valid()

    method Request(p: Process)
        requires Valid() && p in P && cs[p] == Thinking
        modifies this
        ensures Valid()
    {}

    method Enter(p: Process)
        requires Valid() && p in P && cs[p] == Hungry
        modifies this
        ensures Valid()
    {}

    method Leave(p: Process)
        requires Valid() && p in P && cs[p] == Eating
        modifies this
        ensures Valid()
    {}

    // correctness: no two process are in eating state at same time
    // prove that invariant implies condition
    lemma MutualExclusion(p: Process, q: Process)
        requires Valid() && p in P && q in P // if system is in valid state and both p, q are processes
        requires cs[p] == Eating && cs[q] == Eating // both p, q are in Eating state
        ensures p == q // p and q are the same process       
}

