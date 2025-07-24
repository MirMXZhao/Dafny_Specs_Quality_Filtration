// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// This file contains an example chain of module refinements, starting from a
// simple interface M0 to an implementation M3. Module Client.Test() is
// verified against the original M0 module. Module CachedClient instantiates
// the abstract import of M0 with the concrete module M3, and then gets to
// reuse the proof done in Client.
//
// At a sufficiently abstract level, the concepts used are all standard.
// However, it can be tricky to set these things up in Dafny, if you want
// the final program to be a composition of smaller refinement steps.
//
// Textually, refinement modules in Dafny are written with "...", rather
// than by repeating the program text from the module being refined.
// This can be difficult to both author and read, so this file can be
// used as a guide for what to aim for. Undoubtedly, use of the /rprint:-
// option on the command line will be useful, since it lets you see what
// all the ...'s expand to.
//
// As a convenience, this program also uses a second experimental feature,
// namely the preprocessing requested by :autocontracts, which supplies
// much of the boilerplate specifications that one uses with the
// dynamic-frames idiom in Dafny. This feature was designed to reduce clutter
// in the program text, but can increase the mystery behind what's really
// going on. Here, too, using the /rprint:- option will be useful, since
// it shows the automatically generated specifications and code.
//
// (For another example that uses these features, see Test/dafny2/StoreAndRetrieve.dfy.)


// give the method signatures and specs
abstract module M0 {
  class {:autocontracts} Container<T(==)> {
    ghost var Contents: set<T>
    ghost predicate Valid() {}
    ghost predicate {} Valid'()
      reads this, Repr
    constructor ()
      ensures Contents == {}
    method Add(t: T)
      ensures Contents == old(Contents) + {t}
    method Remove(t: T)
      ensures Contents == old(Contents) - {t}
    method Contains(t: T) returns (b: bool)
      ensures Contents == old(Contents)
      ensures b <==> t in Contents
  }
}

// provide bodies for the methods
abstract module M1 refines M0 {
  class Container<T(==)> ... {
    constructor... {}
    method Add... {}
    method Remove... {}
    method Contains... {}
  }
}

// implement the set in terms of a sequence
abstract module M2 refines M1 {
  class Container<T(==)> ... {
    var elems: seq<T>
    ghost predicate Valid'...
    {}
    ghost predicate {} Valid''()
      reads this, Repr
    method FindIndex(t: T) returns (j: nat)
      ensures j <= |elems|
      ensures if j < |elems| then elems[j] == t else t !in elems
    {}

    constructor... {}
    method Add... {}
    method Remove... {}
    method Contains... {}
  }
}

// implement a cache

module M3 refines M2 {
  datatype Cache<T> = None | Some(index: nat, value: T)
  class Container<T(==)> ... {
    var cache: Cache<T>
    ghost predicate Valid''... {}
    constructor... {}
    method FindIndex... {}
    method Add... {
      ...;
    }
    method Remove... {}
  }
}

// here a client of the Container
abstract module Client {
  import M : M0
  method Test() {}
}

module CachedClient refines Client {
  import M = M3
  method Main() {
    Test();
  }
}

