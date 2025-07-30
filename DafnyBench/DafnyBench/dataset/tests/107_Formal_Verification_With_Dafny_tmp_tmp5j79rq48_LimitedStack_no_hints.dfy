class LimitedStack{
 
      var capacity : int;
      var arr : array<int>;
      var top : int;

      predicate Valid()
      reads this;
      {}

      predicate Empty()
      reads this`top;
      {}

      predicate Full()
      reads this`top, this`capacity;
      {}
  
      method Init(c : int)
      modifies this;
      requires c > 0
      ensures Valid() && Empty() && c == capacity
      ensures fresh(arr);
      {}

      method isEmpty() returns (res : bool)
      ensures res == Empty()
      {}

      method Peek() returns (elem : int) 
      requires Valid() && !Empty()
      ensures elem == arr[top]
      {}

      method Push(elem : int)
      modifies this`top, this.arr 
      requires Valid()
      requires !Full() 
      ensures Valid() && top == old(top) + 1 && arr[top] == elem
      ensures !old(Empty()) ==> forall i : int :: 0 <= i <= old(top)  ==> arr[i] == old(arr[i]);
      {}

      method Pop() returns (elem : int)
      modifies   this`top
      requires Valid() && !Empty()  
      ensures Valid()  && top == old(top) - 1 
      ensures elem == arr[old(top)] 
      {}

      method Shift()
      requires Valid() && !Empty();
      ensures Valid();
      ensures forall i : int :: 0 <= i < capacity - 1 ==> arr[i] == old(arr[i + 1]);
      ensures top == old(top) - 1;
      modifies this.arr, this`top;
      {}

      method Push2(elem : int)
      modifies this.arr, this`top
      requires Valid()
      ensures Valid() && !Empty() 
      ensures arr[top] == elem
      ensures old(!Full()) ==> top == old(top) + 1 && old(Full()) ==> top == old(top)
      ensures ((old(Full()) ==> arr[capacity - 1] == elem)  && (old(!Full()) ==> (top == old(top) + 1 && arr[top] == elem) ))
      ensures old(Full()) ==> forall i : int :: 0 <= i < capacity - 1 ==> arr[i] == old(arr[i + 1]);
      {}

}

////////TESTS////////

method TestInit1() {
  var stack := new LimitedStack;
  stack.Init(5);
  assert stack.capacity == 5;
  assert stack.Valid();
  assert stack.Empty();
}

method TestInit2() {
  var stack := new LimitedStack;
  stack.Init(10);
  assert stack.capacity == 10;
  assert stack.Valid();
  assert stack.Empty();
}

method TestIsEmpty1() {
  var stack := new LimitedStack;
  stack.Init(3);
  var res := stack.isEmpty();
  assert res == true;
}

method TestIsEmpty2() {
  var stack := new LimitedStack;
  stack.Init(5);
  stack.Push(42);
  var res := stack.isEmpty();
  assert res == false;
}

method TestPeek1() {
  var stack := new LimitedStack;
  stack.Init(3);
  stack.Push(42);
  var elem := stack.Peek();
  assert elem == 42;
}

method TestPeek2() {
  var stack := new LimitedStack;
  stack.Init(5);
  stack.Push(100);
  var elem := stack.Peek();
  assert elem == 100;
}

method TestPush1() {
  var stack := new LimitedStack;
  stack.Init(3);
  var oldTop := stack.top;
  stack.Push(25);
  assert stack.Valid();
  assert stack.top == oldTop + 1;
  assert stack.arr[stack.top] == 25;
}

method TestPush2() {
  var stack := new LimitedStack;
  stack.Init(5);
  var oldTop := stack.top;
  stack.Push(75);
  assert stack.Valid();
  assert stack.top == oldTop + 1;
  assert stack.arr[stack.top] == 75;
}

method TestPop1() {
  var stack := new LimitedStack;
  stack.Init(3);
  stack.Push(30);
  var oldTop := stack.top;
  var elem := stack.Pop();
  assert stack.Valid();
  assert stack.top == oldTop - 1;
  assert elem == 30;
}

method TestPop2() {
  var stack := new LimitedStack;
  stack.Init(4);
  stack.Push(60);
  var oldTop := stack.top;
  var elem := stack.Pop();
  assert stack.Valid();
  assert stack.top == oldTop - 1;
  assert elem == 60;
}

method TestShift1() {
  var stack := new LimitedStack;
  stack.Init(3);
  stack.Push(10);
  stack.Push(20);
  var oldTop := stack.top;
  stack.Shift();
  assert stack.Valid();
  assert stack.top == oldTop - 1;
}

method TestShift2() {
  var stack := new LimitedStack;
  stack.Init(4);
  stack.Push(15);
  stack.Push(25);
  stack.Push(35);
  var oldTop := stack.top;
  stack.Shift();
  assert stack.Valid();
  assert stack.top == oldTop - 1;
  assert stack.arr[0] == 25;
  assert stack.arr[1] == 35;
}

method TestPush21() {
  var stack := new LimitedStack;
  stack.Init(2);
  stack.Push2(50);
  assert stack.Valid();
  assert !stack.Empty();
  assert stack.arr[stack.top] == 50;
}

method TestPush22() {
  var stack := new LimitedStack;
  stack.Init(2);
  stack.Push(10);
  stack.Push(20);
  var oldTop := stack.top;
  stack.Push2(80);
  assert stack.Valid();
  assert !stack.Empty();
  assert stack.arr[stack.top] == 80;
  assert stack.top == oldTop;
  assert stack.arr[0] == 20;
