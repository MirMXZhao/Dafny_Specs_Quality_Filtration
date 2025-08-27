type Key = seq<int>
type Value = seq<int>

type Hashtable = map<Key, Value>
function HashtableLookup(h: Hashtable, k: Key): Value

lemma HashtableAgreement(h1:Hashtable, h2:Hashtable, k:Key)
  requires forall k :: HashtableLookup(h1,k) == HashtableLookup(h2,k) {}