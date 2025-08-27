module ModelingTM {
    type ProcessId = nat
    type MemoryObject = nat
    type TimeStamp = nat

    class Operation {}

    class Transaction {}

    class ProcessState {}

    class TMSystem {}
    

    method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
        requires pid in input.txQueues
        requires pid in input.procStates
        requires input.validSystem()
        ensures system.validSystem()
    {}
}

////////TESTS////////

method TestStep1() {
  var input := new TMSystem;
  var pid: ProcessId := 0;
  assume pid in input.txQueues;
  assume pid in input.procStates;
  assume input.validSystem();
  var system := Step(input, pid);
  assert system.validSystem();
}

method TestStep2() {
  var input := new TMSystem;
  var pid: ProcessId := 1;
  assume pid in input.txQueues;
  assume pid in input.procStates;
  assume input.validSystem();
  var system := Step(input, pid);
  assert system.validSystem();
}
