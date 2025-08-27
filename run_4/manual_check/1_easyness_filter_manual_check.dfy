// Kept File 1:
// filename: Clover_longest_prefix_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_longest_prefix_no_hints.dfy
// keepToss: KEEP
// reasoning: This requires iterative comparison logic to find the longest matching prefix, which is not a direct formula.

method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{}

// Kept File 2:
// filename: dafny-synthesis_task_id_566_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_566_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification involves multiple interconnected functions and lemmas for digit manipulation and mathematical operations, which is not a direct formula.

method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{}

//lemma DivIsZero()
//  ensures forall num, den : nat :: den >= 1 && num < den ==> num/den == 0

lemma X(x: nat)
  ensures Power10(NumberOfDigits(x)) > x
{}

lemma NumberIdentity(number: nat, pmax: nat)
  requires pmax == Power10(NumberOfDigits(number))
  ensures number == number % pmax
{}


lemma InIntValues(n: nat)
  ensures 0 in IntValues(n)
  ensures n in IntValues(n)
  ensures n/10 in IntValues(n)
{}

// ghost function ValuesOfn(number: nat, ndigits: nat) : (r: seq<nat>)
// {}

ghost function IntValues(n: int) : (r: seq<int>)
  requires n >= 0
  ensures 0 in r
  ensures n in r
  ensures n/10 in r
  //    ensures forall p :: p in powersOfTen ==> n/p in r
{}

function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{}

function NumberToSeq(number: int) : seq<int>
  requires number >= 0
{}

function Sum(digits: seq<int>) : int
{}

function SumDigits(n: nat) : nat
{}

function SumDigitsRecursive(n: nat, p: nat) : (r: nat)
{}

function NumberOfDigits(n: nat) : (r: nat)
  ensures r >= 1
  ensures r == 1 <==> 0 <= n <= 9
{}
// Kept File 3:
// filename: stunning-palm-tree_tmp_tmpr84c2iwh_ch5_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/stunning-palm-tree_tmp_tmpr84c2iwh_ch5_no_hints.dfy
// keepToss: KEEP
// reasoning: This involves complex structural recursion, pattern matching, and logical reasoning about expression evaluation rather than being a direct formula.

function More(x: int): int {}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{}

method ExampleLemmaUse(a: int) {}

// Ex 5.0
method ExampleLemmaUse50(a: int) {}

// Ex 5.1
method ExampleLemmaUse51(a: int) {}

// Ex 5.6
function Ack(m: nat, n: nat): nat {}

lemma {:induction false} Ack1n(m: nat, n: nat)
  requires m == 1
  ensures Ack(m, n) == n + 2
{}

// Ex 5.5
function Reduce(m: nat, x: int): int {}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
{}

// 5.5.1
lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
{
  if m == 0 {  // trivial
  }
  else {
    calc {
      Reduce(m, x);
    ==  // defn
      Reduce(m / 2, x + 1) - m;
    >= { ReduceLowerBound(m/2, x+1);
      x + 1 - 2 * m;
    >  // arith
      x - 2 * m;
    }
  }
}


// ------------------------------------------------------------------------------
// ----- Expr Eval --------------------------------------------------------------
// ------------------------------------------------------------------------------

// 5.8.0

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Mul | Add
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e: Expr, env: map<string, nat>): nat
{
  match e {
    case Const(c) => c
    case Var(s) => if s in env then env[s] else 0
    case Node(op, args) => EvalList(op, args, env)
  }
}

// intro'd in 5.8.1
function Unit(op: Op): nat {
  match op case Add => 0 case Mul => 1
}

function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
{
  match args {
    case Nil => Unit(op)
    case Cons(e, tail) =>
      var v0, v1 := Eval(e, env), EvalList(op, tail, env);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1
  }
}

function Substitute(e: Expr, n: string, c: nat): Expr
{
  match e
  case Const(_) => e
  case Var(s) => if s == n then Const(c) else e
  case Node(op, args) => Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{
  match es
  case Nil => Nil
  case Cons(head, tail) => Cons(Substitute(head, n, c), SubstituteList(tail, n, c))
}

lemma {:induction false} EvalSubstituteCorrect(e: Expr, n: string, c: nat, env: map<string, nat>)
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
{
  match e
  case Const(_) => {}
  case Var(s) => {
    calc {
      Eval(Substitute(e, n, c), env);
      Eval(if s == n then Const(c) else e, env);
      if s == n then Eval(Const(c), env) else Eval(e, env);
      if s == n then c else Eval(e, env);
      if s == n then c else Eval(e, env[n := c]);
      if s == n then Eval(e, env[n := c]) else Eval(e, env[n := c]);
      Eval(e, env[n := c]);
    }
  }
  case Node(op, args) => {
    EvalSubstituteListCorrect(op, args, n, c, env);
  }
}

lemma {:induction false} EvalSubstituteListCorrect(op: Op, args: List<Expr>, n: string, c: nat, env: map<string, nat>)
  ensures EvalList(op, SubstituteList(args, n, c), env) == EvalList(op, args, env[n := c])
{
  match args
  case Nil => {}
  case Cons(head, tail) => {
    // Ex 5.15
    calc {
      EvalList(op, SubstituteList(args, n, c), env);
    ==  // defn SubstituteList
      EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
    == // unfold defn EvalList
      EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
    ==
      (match op
       case Add => Eval(Substitute(head, n, c), env) + EvalList(op, SubstituteList(tail, n, c), env)
       case Mul => Eval(Substitute(head, n, c), env) * EvalList(op, SubstituteList(tail, n, c), env));
    == { EvalSubstituteCorrect(head, n, c, env); }
      (match op
       case Add => Eval(head, env[n := c]) + EvalList(op, SubstituteList(tail, n, c), env)
       case Mul => Eval(head, env[n := c]) * EvalList(op, SubstituteList(tail, n, c), env));
    == { EvalSubstituteListCorrect(op, tail, n, c, env); }
      (match op
       case Add => Eval(head, env[n := c]) + EvalList(op, tail, env[n := c])
       case Mul => Eval(head, env[n := c]) * EvalList(op, tail, env[n := c]));
    == // fold defn Eval/EvalList
      EvalList(op, args, env[n := c]);
    }
  }
}

// Ex 5.16
lemma EvalEnv(e: Expr, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, env[n]), env)
{
  match e
  case Const(_) => {}
  case Var(s) => {}
  case Node(op, args) => {
    match args
    case Nil => {}
    case Cons(head, tail) => { EvalEnv(head, n, env); EvalEnvList(op, tail, n, env); }
  }
}

lemma EvalEnvList(op: Op, es: List<Expr>, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures EvalList(op, es, env) == EvalList(op, SubstituteList(es, n, env[n]), env)
{
  match es
  case Nil => {}
  case Cons(head, tail) => { EvalEnv(head, n, env); EvalEnvList(op, tail, n, env); }
}

// Ex 5.17
lemma EvalEnvDefault(e: Expr, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{
  match e
  case Const(_) => {}
  case Var(s) => {}
  case Node(op, args) => {
    calc {
      Eval(Substitute(e, n, 0), env);
      EvalList(op, SubstituteList(args, n, 0), env);
    == { EvalEnvDefaultList(op, args, n, env); }
      EvalList(op, args, env);
      Eval(e, env);
    }
  }
}

lemma EvalEnvDefaultList(op: Op, args: List<Expr>, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures EvalList(op, args, env) == EvalList(op, SubstituteList(args, n, 0), env)
{
  match args
  case Nil => {}
  case Cons(head, tail) => { EvalEnvDefault(head, n, env); EvalEnvDefaultList(op, tail, n, env); }
}

// Ex 5.18
lemma SubstituteIdempotent(e: Expr, n: string, c: nat)
  ensures Substitute(Substitute(e, n, c), n, c) == Substitute(e, n, c)
{
  match e
  case Const(_) => {}
  case Var(_) => {}
  case Node(op, args) => { SubstituteListIdempotent(args, n, c); }
}

lemma SubstituteListIdempotent(args: List<Expr>, n: string, c: nat)
  ensures SubstituteList(SubstituteList(args, n, c), n, c) == SubstituteList(args, n, c)
{
  match args
  case Nil => {}
  case Cons(head, tail) => { SubstituteIdempotent(head, n, c); SubstituteListIdempotent(tail, n, c); }
}

// 5.8.1
// Optimization is correct

function Optimize(e: Expr): Expr
  // intrinsic
  // ensures forall env: map<string, nat> :: Eval(Optimize(e), env) == Eval(e, env)
{
  if e.Node? then
    var args := OptimizeAndFilter(e.args, Unit(e.op));
    Shorten(e.op, args)
  else
    e
}

lemma OptimizeCorrect(e: Expr, env: map<string, nat>)
  ensures Eval(Optimize(e), env) == Eval(e, env)
{
  if e.Node? {
    OptimizeAndFilterCorrect(e.args, e.op, env); 
    ShortenCorrect(OptimizeAndFilter(e.args, Unit(e.op)), e.op, env); 
    // calc {
    //   Eval(Optimize(e), env);
    // == // defn Optimize
    //   Eval(Shorten(e.op, OptimizeAndFilter(e.args, Unit(e.op))), env);
    // == { ShortenCorrect(OptimizeAndFilter(e.args, Unit(e.op)), e.op, env); }
    //   Eval(Node(e.op, OptimizeAndFilter(e.args, Unit(e.op))), env);
    // == { OptimizeAndFilterCorrect(e.args, e.op, env); }
    //   Eval(e, env);
    // }
  }
}

function OptimizeAndFilter(args: List<Expr>, u: nat): List<Expr>
  // intrinsic
  // ensures forall op: Op, env: map<string, nat> :: u == Unit(op) ==> Eval(Node(op, OptimizeAndFilter(args, u)), env) == Eval(Node(op, args), env)
{
  match args
  case Nil => Nil
  case Cons(head, tail) =>
    var hd, tl := Optimize(head), OptimizeAndFilter(tail, u);
    if hd == Const(u) then tl else Cons(hd, tl)
}

lemma OptimizeAndFilterCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env) == Eval(Node(op, args), env)
{
  match args
  case Nil => {}
  case Cons(head, tail) => {
    OptimizeCorrect(head, env);
    OptimizeAndFilterCorrect(tail, op, env);
    // var hd, tl := Optimize(head), OptimizeAndFilter(tail, Unit(op));
    // var u := Unit(op);
    // if hd == Const(u) {
    //   calc {
    //     Eval(Node(op, OptimizeAndFilter(args, u)), env);
    //   ==
    //     EvalList(op, OptimizeAndFilter(args, u), env);
    //   == { assert OptimizeAndFilter(args, u) == tl; }
    //     EvalList(op, tl, env);
    //   ==
    //     Eval(Node(op, tl), env);
    //   == { EvalListUnitHead(hd, tl, op, env); }
    //     Eval(Node(op, Cons(hd, tl)), env);
    //   == { OptimizeCorrect(head, env); OptimizeAndFilterCorrect(tail, op, env); }
    //     Eval(Node(op, args), env);
    //   }
    // } else {
    //   calc {
    //     Eval(Node(op, OptimizeAndFilter(args, u)), env);
    //   ==
    //     EvalList(op, OptimizeAndFilter(args, u), env);
    //   == { assert OptimizeAndFilter(args, u) == Cons(hd, tl); }
    //     EvalList(op, Cons(hd, tl), env);
    //   ==
    //     Eval(Node(op, Cons(hd, tl)), env);
    //   == { OptimizeCorrect(head, env); OptimizeAndFilterCorrect(tail, op, env); }
    //     Eval(Node(op, args), env);
    //   }
    // }
  }
}

lemma EvalListUnitHead(head: Expr, tail: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(head, env) == Unit(op) ==> EvalList(op, Cons(head, tail), env) == EvalList(op, tail, env)
{
  // Note: verifier can prove the whole lemma with empty body!
  var ehead, etail := Eval(head, env), EvalList(op, tail, env);
  if ehead == Unit(op) {
    match op
    case Add => {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==  // defn EvalList
          ehead + etail;
        == // { assert ehead == Unit(Add); assert Unit(Add) == 0; }
          etail;
        }
    }
    case Mul => {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==  // defn EvalList
          ehead * etail;
        == // { assert ehead == 1; }
          etail;
        }
    }
  }
}

function Shorten(op: Op, args: List<Expr>): Expr {
  match args
  case Nil => Const(Unit(op))
  // shorten the singleton list
  case Cons(head, Nil) => head
  // reduce units from the head
  case _ => Node(op, args)
}

lemma ShortenCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Shorten(op, args), env) == Eval(Node(op, args), env)
{
  match args
  case Nil => {}
  case Cons(head, Nil) => {
    calc {
      Eval(Node(op, args), env);
      EvalList(op, Cons(head, Nil), env);
      Eval(head, env);
      /* Eval(Shorten(op, Cons(head, Nil)), env); */
      /* Eval(Shorten(op, args), env); */
    }
  }
  case _ => {}
}

// Kept File 4:
// filename: Software-Verification_tmp_tmpv4ueky2d_Remove Duplicates from Sorted Array_remove_duplicates_from_sorted_array_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Software-Verification_tmp_tmpv4ueky2d_Remove Duplicates from Sorted Array_remove_duplicates_from_sorted_array_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification requires logic to remove duplicates from a sorted array, which is not a direct formula.

method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{}


// Helper predicate
predicate is_sorted(nums: seq<int>)
{}

predicate is_sorted_and_distinct(nums: seq<int>)
{}


// Kept File 5:
// filename: dafny_experiments_tmp_tmpz29_3_3i_circuit_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny_experiments_tmp_tmpz29_3_3i_circuit_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification involves complex data structure manipulation for combining circuit representations, not a direct formula.

module Base
{
    // We want to represent circuits.
    // A Circuit is composed of nodes.
    // Each node can have input ports and output ports.

    // The ports are represented just by the index of the node, and the index
    // of the port on the node.
    datatype INodePort = inodeport(node_id: nat, port_id: nat)
    datatype ONodePort = onodeport(node_id: nat, port_id: nat)

    // Currently the nodes can just be Xor, And or Identity gates.
    datatype Node =
        Xor |
        And |
        Ident

    // The number of input ports for each kind of node.
    function n_iports (node: Node): nat
    {}

    // The number of output ports for each kind of node.
    function n_oports (node: Node): nat
    {}

    // A circuit is represented by the nodes and the connections between the nodes.
    // Each output port can go to many input ports.
    // But each input port can only be connected to one output port.
    datatype Circuit = Circ(
        nodes: seq<Node>,
        backconns: map<INodePort, ONodePort>
        )

    // Just checking that the port and node indices mentioned in the connections are sane.
    predicate WellformedBackConns(c: Circuit)
    {}

    predicate WellformedINP(c: Circuit, inp: INodePort)
    {}

    predicate WellformedONP(c: Circuit, onp: ONodePort)
    {}

    // All input ports in a circuit.
    function AllINPs(c: Circuit): set<INodePort>
        ensures forall inp :: inp in AllINPs(c) ==> WellformedINP(c, inp)
    {}

    // All output ports in a circuit.
    function AllONPs(c: Circuit): set<ONodePort>
        ensures forall onp :: onp in AllONPs(c) ==> WellformedONP(c, onp)
    {}

    ghost predicate Wellformed(c: Circuit)
    {}
}

module Utils
{}

module BackwardConnections
{
    import opened Base
    import opened Utils

    // This is used when we are trying to create a new circuit by combining two existing circuits.
    // This function takes care of combining the backwards connections.
    // Because the node_indices of the two circuits are just natural numbers when we combine the
    // two circuits we need to shift the node indices of the second circuit so that they don't clash.
    // We do this by adding `offset` to the node indices.
    function CombineBackconns(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>): (result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
    {}

    lemma CombineBackconnsHelper(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        ensures
            forall inp :: inp in bc1 ==> (
                inp in result &&
                result[inp] == bc1[inp])
        ensures
            forall inp :: inp in bc2 ==> (
                inodeport(inp.node_id+offset, inp.port_id) in result &&
                result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id))
    {}

    lemma CombineBackconnsHelper2(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>, inp: INodePort)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        requires inp in bc2
        ensures
            inodeport(inp.node_id+offset, inp.port_id) in result
        ensures
            result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id)
    {}
}


module CombineCircuits {

    import opened Base
    import BackwardConnections
    import opened Utils

    // Combine two circuits into a new circuit.
    // This is a bit ugly because we have to offset the node indices of the
    // second circuit by |c1.nodes|.
    function CombineCircuits(c1: Circuit, c2: Circuit): (r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {}

    // Check that Circuit c2 contains a subcircuit that corresponds to c1 getting mapped with the
    // `node_map` function.
    predicate IsEquivalentCircuit(node_is_member: nat->bool, node_map: nat-->nat, c1: Circuit, c2: Circuit)
        requires forall inp :: inp in c1.backconns && node_is_member(inp.node_id) ==> node_is_member(c1.backconns[inp].node_id)
        requires forall n :: node_is_member(n) ==> node_map.requires(n)
    {}

    // Check that for every input port and output port in the combined Circuit, they can be assigned
    // to a port in one of the two source circuits.
    predicate CanBackAssign(c1: Circuit, c2: Circuit, r: Circuit, is_in_c1: nat->bool, is_in_c2: nat-> bool,
                            map_r_to_c1: nat->nat, map_r_to_c2: nat-->nat)
        requires forall a :: is_in_c1(a) ==> map_r_to_c1.requires(a)
        requires forall a :: is_in_c2(a) ==> map_r_to_c2.requires(a)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {}

    lemma CombineCircuitsCorrectHelper(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
    {}


    lemma CombineCircuitsCorrectC1(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            // The original c1 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            // This subset of r has an image in c1.
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1)
    {
    }

    lemma CombineCircuitsCorrect(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            // The original c1 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            // This subset of r has an image in c1.
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1) &&

            // The original c2 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a+offset, c2, r) &&
/*
            FIXME: These have been commented out for now
                   otherwise it takes longer than 20s to solve.
            // All ports in r have equivalents in either c1 or c2.
            CanBackAssign(c1, c2, r, a=>a < offset, a=> a >= offset, a=>a, a requires a >= offset => sub(a, offset)) &&
            // This subset of r has an image in c2.
            IsEquivalentCircuit(a=>a >= offset, a requires a >= offset => sub(a, offset), r, c2) &&
*/
            true
    {}
}

// Kept File 6:
// filename: Clover_online_max_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_online_max_no_hints.dfy
// keepToss: KEEP
// reasoning: This involves finding a position based on comparisons and conditions across array elements, which is not a direct formula.

method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{}


// Kept File 7:
// filename: Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// keepToss: KEEP
// reasoning: This involves comparing multisets of characters which is not a direct formula.

method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}


// Kept File 8:
// filename: MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification involves multiple algorithmic approaches (recursive, iterative, optimized) with different complexity requirements, not a direct formula.

/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{}

// A simple test case to make sure the specification is adequate.
method testPowerIter(){}

method testPowerOpt(){}

// Kept File 9:
// filename: SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification requires iterating through an array and modifying elements based on a condition, which is not a direct formula.

// successfully verifies
method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{}

// Kept File 10:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue67_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue67_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification involves class definitions, predicates, and method signatures with modifies clauses, which is not a direct formula.

// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

predicate Q(x: Node)
predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
{}


// Kept File 11:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification defines multiple predicates, functions, and lemmas for interval operations that require complex logical reasoning rather than being a direct formula.

/* Here's a small but realistic setting where you could use Dafny.

   The setting is that we're implementing an interval library that manages a
   data structure with a low and a high value. It implements some computations
   on intervals, and we want to make sure those are right.
 */

// Interval is the Dafny model of the data structure itself. We're using `real`
// here for the numbers; the specifics don't really matter, as long as we can
// compare them with <.
datatype Interval = Interval(lo: real, hi: real)

// Contains is one of the core operations on intervals, both because we support
// it in the API and because in some ways it defines what the interval means.
predicate contains(i: Interval, r: real) {}

// We also provide a way to check if an interval is empty.
predicate empty(i: Interval) {
  i.lo > i.hi
}

/* Now we can already do our first proof! Empty is a way to check if an interval
 * doesn't contain any numbers - let's prove that empty and contains agree with
 * each other. */

lemma empty_ok(i: Interval)
  // this is the sort of property that's easy to express logically but hard to test for
  ensures empty(i) <==> !exists r :: contains(i, r)
{}

// min and max are just helper functions for the implementation
function min(r1: real, r2: real): real {}

function max(r1: real, r2: real): real {}

/* The first complicated operation we expose is a function to intersect two
 * intervals. It's not so easy to think about whether this is correct - for
 * example, does it handle empty intervals correctly? Maybe two empty intervals
 * could intersect to a non-empty one? */

function intersect(i1: Interval, i2: Interval): Interval {}

// This theorem proves that intersect does exactly what we wanted it to, using
// `contains` as the specification.
lemma intersect_ok(i1: Interval, i2: Interval)
  ensures forall r :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
{
}

/* Next we'll define the union of intervals. This is more complicated because if
 * the intervals have no overlap, a single interval can't capture their union
 * exactly. */

// Intersect gives us an easy way to define overlap, and we already know it
// handles empty intervals correctly.
predicate overlap(i1: Interval, i2: Interval) {}

lemma overlap_ok(i1: Interval, i2: Interval)
  ensures overlap(i1, i2) <==> exists r :: contains(i1, r) && contains(i2, r)
{}

// We'll give this function a precondition so that it always does the right thing.
function union(i1: Interval, i2: Interval): Interval
  requires overlap(i1, i2)
{}

// We can prove union correct in much the same way as intersect, with a similar
// specification, although notice that now we require that the intervals
// overlap.
lemma union_ok(i1: Interval, i2: Interval)
  requires overlap(i1, i2)
  ensures forall r :: contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
{
}

// Though not used elsewhere here, if two intervals overlap its possible to show
// that there's a common real contained in both of them. We also show off new
// syntax: this lemma returns a value which is used in the postcondition, and
// which the calling lemma can make use of.
lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  requires overlap(i1, i2)
  ensures contains(i1, r) && contains(i2, r)
{}

/* One extension you might try is adding is an operation to check if an interval
 * is contained in another and proving that correct. Or, try implementing a
 * similar library for 2D rectangles. */


// Kept File 12:
// filename: Clover_rotate_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_rotate_no_hints.dfy
// keepToss: KEEP
// reasoning: This involves array manipulation with modular arithmetic indexing logic, which is not a direct formula.

method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
{}
// Kept File 13:
// filename: dafny-synthesis_task_id_591_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_591_no_hints.dfy
// keepToss: KEEP
// reasoning: This involves array manipulation and conditional logic based on array bounds, which is not a direct formula.

method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{}
// Kept File 14:
// filename: dafny-synthesis_task_id_750_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_750_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification involves sequence manipulation logic with multiple constraints on ordering and element preservation, which is not a direct formula.

method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
    r := l + [t];
}
// Kept File 15:
// filename: Dafny_Programs_tmp_tmp99966ew4_trig_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Dafny_Programs_tmp_tmp99966ew4_trig_no_hints.dfy
// keepToss: KEEP
// reasoning: This involves logical reasoning about predicates and quantifiers, not a direct formula.

predicate P(x: int)

predicate Q(x: int)

method test()
    requires forall x {:trigger P(x)} :: P(x) && Q(x)
    ensures Q(0)
{
}

// Tossed File 1:
// filename: dafny-synthesis_task_id_14_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_14_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a direct formula for calculating triangular prism volume with no programming logic beyond the mathematical equation.
method TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{}


// Tossed File 2:
// filename: Dafny_tmp_tmp0wu8wmfr_tests_F1a_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Dafny_tmp_tmp0wu8wmfr_tests_F1a_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a direct formula - the Mid method simply computes the midpoint using the formula (p+q)/2.
method F() returns ( r: int)
    ensures r <= 0
{
    r := 0;
}

method Main() 
{}


method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;

{
    m := (p+q)/2;
}



// Tossed File 3:
// filename: Clover_triple3_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_triple3_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that simply multiplies the input by 3.
method Triple (x:int) returns (r:int)
  ensures r==3*x
{}



// Tossed File 4:
// filename: dafny-synthesis_task_id_242_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_242_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that simply returns the length of a string with no programming logic or reasoning required.
method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}


// Tossed File 5:
// filename: Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_Cube_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that simply computes n cubed with no programming logic or reasoning required.
method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
{}



// Tossed File 6:
// filename: dafny-synthesis_task_id_139_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_139_no_hints.dfy
// keepToss: TOSS
// reasoning: This specification is just a direct formula for calculating circumference using the standard mathematical formula C = 2πr.
method CircleCircumference(radius: real) returns (circumference: real)
    requires radius > 0.0
    ensures circumference == 2.0 * 3.14159265358979323846 * radius
{}


