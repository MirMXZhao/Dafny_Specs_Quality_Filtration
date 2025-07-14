module ModelingTM {
    type ProcessId = nat
    type MemoryObject = nat
    type TimeStamp = nat

    class Operation {}

    class Transaction {}

    // Process state : transaction progress and process memory.
    class ProcessState {
        // currentTx : id of tx being processed. txs.size() means done.
        const currentTx: nat
        // currentOp :
        //      - tx.ops.size() represents tryCommit operation.
        //      - -1 represents abort operation
        //      - values in between represent read and write operations
        const currentOp: int
        // sub-operations of the operation, see the step function
        const currentSubOp: nat

        // Set of read objects with original observed timestamp.
        const readSet: map<MemoryObject, TimeStamp>
        // Set of written objects.
        const writeSet: set<MemoryObject>

        constructor () {}

        constructor nextSubOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp + 1
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {}

        constructor nextOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp + 1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {}

        constructor abortTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == -1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {}

        constructor restartTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {}

        constructor nextTx(that: ProcessState)
            ensures this.currentTx == that.currentTx + 1
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {}

        constructor addToReadSet(that: ProcessState, obj: MemoryObject, ts: TimeStamp)
            ensures currentTx == that.currentTx
            ensures currentOp == that.currentOp
            ensures currentSubOp == that.currentSubOp
            ensures readSet.Keys == that.readSet.Keys + {obj}
                && readSet[obj] == ts
                && forall o :: o in readSet && o != obj ==> readSet[o] == that.readSet[o]
            ensures writeSet == that.writeSet
        {}

        constructor addToWriteSet(that: ProcessState, obj: MemoryObject)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet + {obj}
        {}
    }

    class TMSystem {}
    

    method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
        requires pid in input.txQueues
        requires pid in input.procStates
        requires input.validSystem()
        ensures system.validSystem()
    {}
}

