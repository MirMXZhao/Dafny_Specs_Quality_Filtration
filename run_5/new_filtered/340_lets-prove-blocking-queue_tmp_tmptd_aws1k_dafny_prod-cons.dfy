module ProdCons {

    type Process(==) 

    type T

    class ProdCons { 

        const P: set<Process>

        var maxBufferSize : nat 

        var buffer : seq<T> 

        predicate valid() 
            reads this
        {
            maxBufferSize > 0 && P != {} &&
            0 <= |buffer| <= maxBufferSize 
        }
        
        constructor (processes: set<Process>, m: nat ) 
            requires processes != {}
            requires m >= 1
            ensures valid()
        {}

        predicate putEnabled(p : Process) 
            reads this
        {
            |buffer| < maxBufferSize
        }

        method put(p: Process, t : T) 
            requires valid()                
            requires putEnabled(p)
            modifies this 
        {}

        predicate getEnabled(p : Process) 
            reads this
        {
            |buffer| >= 1
        }

        method get(p: Process) 
            requires getEnabled(p)
            requires valid()
            ensures |buffer| == |old(buffer)| - 1
            modifies this 
        {}
                
        lemma noDeadlock() 
            requires valid() 
            ensures exists p :: p in P && (getEnabled(p) || putEnabled(p))
        {}
    }
}