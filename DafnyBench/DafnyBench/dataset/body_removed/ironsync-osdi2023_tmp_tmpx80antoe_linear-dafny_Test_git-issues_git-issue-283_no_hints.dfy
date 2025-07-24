// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> =
  | Success(value: T)
  | Failure(error: string)

datatype C = C1 | C2(x: int)

trait Foo
{
  method FooMethod1(r: Result<()>)
    ensures
      match r {}
  {}
  method FooMethod2(r: Result<C>)
    ensures
      match r {}
  {}
  method FooMethod2q(r: Result<C>)
    ensures
      match r {}
  {}
  method FooMethod2r(r: Result<C>)
    ensures
      match r {}
  {}
  method FooMethod3(r: Result<C>)
    ensures
      match r {}
  {}
  method FooMethod4(r: Result<C>)
    ensures
      match r {}
  {}
  method FooMethod5(r: Result<string>)
    ensures
      match r {}
  {}
}

class CL extends Foo {}

method Main() {}

method m(t: Foo) {}

