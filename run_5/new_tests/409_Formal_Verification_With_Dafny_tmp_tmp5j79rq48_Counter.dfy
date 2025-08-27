class Counter {
 
  var value : int ;
  
  constructor init() 
  ensures value == 0;
  {}
  
  method getValue() returns (x:int)
  ensures x == value;
  {}
  
  method inc()
  modifies this`value
  requires value >= 0;
  ensures value == old(value) + 1; 
  {}
  
  method dec()
  modifies this`value
  requires value > 0;
  ensures value == old(value) - 1; 
  {}
}

////////TESTS////////

method TestCounterInit1() {
  var counter := new Counter.init();
  assert counter.value == 0;
}

method TestCounterInit2() {
  var counter := new Counter.init();
  var x := counter.getValue();
  assert x == 0;
}

method TestCounterGetValue1() {
  var counter := new Counter.init();
  counter.value := 5;
  var x := counter.getValue();
  assert x == 5;
}

method TestCounterGetValue2() {
  var counter := new Counter.init();
  counter.value := 10;
  var x := counter.getValue();
  assert x == 10;
}

method TestCounterInc1() {
  var counter := new Counter.init();
  counter.inc();
  assert counter.value == 1;
}

method TestCounterInc2() {
  var counter := new Counter.init();
  counter.value := 3;
  counter.inc();
  assert counter.value == 4;
}

method TestCounterDec1() {
  var counter := new Counter.init();
  counter.value := 5;
  counter.dec();
  assert counter.value == 4;
}

method TestCounterDec2() {
  var counter := new Counter.init();
  counter.value := 1;
  counter.dec();
  assert counter.value == 0;
}
