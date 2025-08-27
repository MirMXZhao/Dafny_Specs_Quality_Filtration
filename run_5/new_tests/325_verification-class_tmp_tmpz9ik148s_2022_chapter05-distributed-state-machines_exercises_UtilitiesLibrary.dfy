module UtilitiesLibrary {
  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {}

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {}

  function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  {}

  lemma SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
  {
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
  {
  }

  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx:int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0<=idx<|theSets|
    ensures member in theSets[idx]
  {}

  datatype Option<T> = Some(value:T) | None

  function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {}

  datatype Direction = North() | East() | South() | West()

  function TurnRight(direction:Direction) : Direction
  {}

  lemma Rotation()
  {}

  function TurnLeft(direction:Direction) : Direction
  {}

  datatype Meat = Salami | Ham
  datatype Cheese = Provolone | Swiss | Cheddar | Jack
  datatype Veggie = Olive | Onion | Pepper
  datatype Order =
      Sandwich(meat:Meat, cheese:Cheese)
    | Pizza(meat:Meat, veggie:Veggie)
    | Appetizer(cheese:Cheese)

}

////////TESTS////////

method TestDropLast1() {
  var result := DropLast([1, 2, 3, 4]);
  assert result == [1, 2, 3];
}

method TestDropLast2() {
  var result := DropLast([5]);
  assert result == [];
}

method TestLast1() {
  var result := Last([1, 2, 3, 4]);
  assert result == 4;
}

method TestLast2() {
  var result := Last([42]);
  assert result == 42;
}

method TestUnionSeqOfSets1() {
  var result := UnionSeqOfSets([{1, 2}, {2, 3}, {3, 4}]);
  assert result == {1, 2, 3, 4};
}

method TestUnionSeqOfSets2() {
  var result := UnionSeqOfSets([{}, {5}, {}]);
  assert result == {5};
}

method TestMapRemoveOne1() {
  var result := MapRemoveOne(map[1 := "a", 2 := "b", 3 := "c"], 2);
  assert result == map[1 := "a", 3 := "c"];
}

method TestMapRemoveOne2() {
  var result := MapRemoveOne(map[5 := "x"], 5);
  assert result == map[];
}

method TestTurnRight1() {
  var result := TurnRight(North());
  assert result == East();
}

method TestTurnRight2() {
  var result := TurnRight(West());
  assert result == North();
}

method TestTurnLeft1() {
  var result := TurnLeft(North());
  assert result == West();
}

method TestTurnLeft2() {
  var result := TurnLeft(South());
  assert result == East();
}
