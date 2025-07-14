datatype List<T> = Nil | Cons(head:T,tail:List<T>)
datatype Option<T> = None | Some(elem:T)

ghost function mem<T>(x:T,l:List<T>) : bool {}

ghost function length<T>(l:List<T>) : int {}

function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
  ensures match list_find(k,l) {}
{}

function list_remove<K(==,!new),V(!new)>(k:K, l:List<(K,V)>) : List<(K,V)>
  ensures forall k',v :: mem((k',v),list_remove(k,l)) <==> (mem((k',v),l) && k != k')
{}


class Hashtable<K(==,!new),V(!new)> {
  var size : int
  var data : array<List<(K,V)>>

  ghost var Repr : set<object>
  ghost var elems : map<K,Option<V>>

  ghost predicate RepInv()
    reads this, Repr
  {}

  ghost predicate valid_hash(data: array<List<(K,V)>>, i: int)
    requires 0 <= i < data.Length
    reads data
  {}


  ghost predicate valid_data(k: K,v: V,elems: map<K, Option<V>>, data: array<List<(K,V)>>)
    reads this, Repr, data
    requires data.Length > 0
  {}


  function hash(key:K) : int
    ensures hash(key) >= 0

  function bucket(k: K, n: int) : int
    requires n > 0
    ensures 0 <= bucket(k, n) < n
  {
    hash(k) % n
  }

  constructor(n:int)
    requires n > 0
    ensures RepInv()
    ensures fresh(Repr-{this})
    ensures elems == map[]
    ensures size == 0
  {}

  method clear()
    requires RepInv()
    ensures RepInv()
    ensures elems == map[]
    ensures fresh(Repr - old(Repr))
    modifies Repr
  {}

  method resize()
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures forall key :: key in old(elems) ==> key in elems
    ensures forall k,v :: k in old(elems) && old(elems)[k] == Some(v) ==> k in elems && elems[k] == Some(v)
    modifies Repr
  {}


  method rehash(l: List<(K,V)>, newData: array<List<(K,V)>>,i: int, oldSize: int, newSize: int)
    requires newData != data
    requires 0 < oldSize == data.Length
    requires newData.Length == 2 * oldSize == newSize
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == i
    requires forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    requires forall k,v :: (
                           if 0 <= bucket(k, oldSize) < i then
                             valid_data(k,v,elems,newData)
                           else if bucket(k, oldSize) == i then
                             ((k in elems && elems[k] == Some(v))
                              <==> mem((k,v), l) || mem((k,v),newData[bucket(k, newSize)]))
                           else
                             !mem((k,v),newData[bucket(k, newSize)]))
    ensures forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    ensures forall k,v ::
              (if 0 <= bucket(k, oldSize) <= i then
                valid_data(k,v,elems,newData)
              else
                !mem((k,v),newData[bucket(k, newSize)]))
    modifies newData
  {}

  method find(k: K) returns (r: Option<V>)
    requires RepInv()
    ensures RepInv()
    ensures match r
            case None => (k !in elems || (k in elems && elems[k] == None))
            case Some(v) => (k in elems && elems[k] == Some(v))
  {}


  method remove(k: K)
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures k !in elems || elems[k] == None
    ensures forall key :: key != k && key in old(elems) ==> key in elems && elems[key] == old(elems[key])
    modifies Repr
  {}

  method add(k:K,v:V)
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures k in elems && elems[k] == Some(v)
    ensures forall key :: key != k && key in old(elems) ==> key in elems
    modifies Repr
  {}

}
