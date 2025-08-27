type Key = seq<int>
type Value = seq<int>

type Hashtable = map<Key, Value>
function HashtableLookup(h: Hashtable, k: Key): Value

lemma HashtableAgreement(h1:Hashtable, h2:Hashtable, k:Key)
  requires forall k :: HashtableLookup(h1,k) == HashtableLookup(h2,k) {}

////////TESTS////////

method TestHashtableLookup1() {
  var h: Hashtable := map[[1, 2] := [3, 4], [5] := [6, 7, 8]];
  var result := HashtableLookup(h, [1, 2]);
  assert result == [3, 4];
}

method TestHashtableLookup2() {
  var h: Hashtable := map[[1] := [2], [3, 4] := [5, 6]];
  var result := HashtableLookup(h, [7, 8]);
  assert result == [];
}
