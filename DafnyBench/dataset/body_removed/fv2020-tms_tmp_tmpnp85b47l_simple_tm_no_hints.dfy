module ModelingTM {
    type ProcessId = nat
    type MemoryObject = nat
    type TimeStamp = nat

    class Operation {}

    class Transaction {}

    // Process state : transaction progress and process memory.
    class ProcessState {}

    class TMSystem {
        // Ordered list of transaction that each process should process
        const txQueues : map<ProcessId, seq<Transaction>>
        // State and memory of processes
        const procStates : map<ProcessId, ProcessState>
        // Dirty objects. (Replaces the object value in a real representation. Used for safety proof)
        const dirtyObjs: set<MemoryObject>
        // Object lock.
        const lockedObjs: set<MemoryObject>
        // Object timestamp. (Incremented at the end of any write transaction)
        const objTimeStamps: map<MemoryObject, nat>

        constructor (q: map<ProcessId, seq<Transaction>>) {}

        constructor initTimestamp(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys ==  that.objTimeStamps.Keys + {obj}
                && objTimeStamps[obj] == 0
                && forall o :: o in objTimeStamps && o != obj ==> objTimeStamps[o] == that.objTimeStamps[o]
        {}
        
        constructor updateState(that: TMSystem, pid: ProcessId, state: ProcessState)
            ensures txQueues == that.txQueues
            ensures procStates.Keys == that.procStates.Keys + {pid}
                && procStates[pid] == state
                && forall p :: p in procStates && p != pid ==> procStates[p] == that.procStates[p]
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {}
        
        constructor markDirty(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs + {obj}
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {}
        
        constructor clearDirty(that: TMSystem, writeSet: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs - writeSet
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {}

        constructor acquireLock(that: TMSystem, o: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs + {o}
            ensures objTimeStamps == that.objTimeStamps
        {}

        constructor releaseLocks(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs - objs
            ensures objTimeStamps ==  that.objTimeStamps
        {}
        
        constructor updateTimestamps(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys == that.objTimeStamps.Keys
                && forall o :: o in that.objTimeStamps ==>
                if(o in objs) then objTimeStamps[o] != that.objTimeStamps[o] else objTimeStamps[o] == that.objTimeStamps[o]
        {}

        predicate stateValid(pid: ProcessId, state: ProcessState)
            requires pid in procStates && state == procStates[pid]
        {}

        predicate validSystem()
        {}
    }
    

    method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
        requires pid in input.txQueues
        requires pid in input.procStates
        requires input.validSystem()
        ensures system.validSystem()
    {}
}

