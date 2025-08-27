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
  method ProcessEmptyResult(r: Result<()>)
    ensures
      match r {
        case Success(()) => true // OK
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(()) => x := 1;
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }
  method ProcessCResultWithMatching(r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true // OK
        case Success(C2(x)) => true // OK
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1()) => x := 1;
      case Success(C2(_)) => x := 2;
      case Failure(e) => x := 3;
    }
    assert x > 0;
    expect x == 1;
  }
  method ProcessCResultWithLocalVariable(r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true // OK
        case Success(C2(x)) => true // OK
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1()) => x := 1;
      case Success(C2(x)) => x := 2;  // x is local variable
      case Failure(e) => x := 3;
    }
    assert x == 0 || x == 1 || x == 3;
    expect x == 0 || x == 1 || x == 3;
  }
  method ProcessCResultWithRealVariable(r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true // OK
        case Success(C2(x)) => true // OK
        case Failure(e) => true
      }
  {
    var x: real := 0.0;
    match r {
      case Success(C1()) => x := 1.0;
      case Success(C2(x)) => x := 2;  // x is local variable
      case Failure(e) => x := 3.0;
    }
    assert x == 0.0 || x == 1.0 || x == 3.0;
    expect x == 0.0 || x == 1.0 || x == 3.0;
  }
  method ProcessCResultWithConstructorPattern(r: Result<C>)
    ensures
      match r {
        case Success(C1) => true // OK
        case Success(C2(x)) => true // OK
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1) => x := 1;
      case Success(C2(_)) => x := 2;  // BUG - problem if _ is x
      case Failure(e) => x := 3;
    }
    assert x > 0;
    expect x == 1;
  }
  method ProcessCResultAsVariable(r: Result<C>)
    ensures
      match r {
        case Success(C2) => true // OK -- C2 is a variable
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C2) => x := 1;
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }
  method ProcessStringResultWithCVariable(r: Result<string>)
    ensures
      match r {
        case Success(C1) => true // OK -- C1 is a variable
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1) => x := 1;
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }
}

class CL extends Foo {}

method Main() {
  var t := new CL;
  CallTestMethods(t);
}

method CallTestMethods(t: Foo) {
  t.ProcessEmptyResult(Result.Success(()));
  t.ProcessCResultWithMatching(Result<C>.Success(C1));
  t.ProcessCResultWithLocalVariable(Result<C>.Success(C1));
  t.ProcessCResultWithRealVariable(Result<C>.Success(C1));
  t.ProcessCResultWithConstructorPattern(Result<C>.Success(C1));
  t.ProcessCResultAsVariable(Result<C>.Success(C1));
  t.ProcessStringResultWithCVariable(Result<string>.Success(""));
  print "Done\n";
}