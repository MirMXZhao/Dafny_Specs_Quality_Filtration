module {} MutableMapDafny {
  trait {:termination false} MutableMapTrait<K(==),V(==)> {
    function content(): map<K, V>
      reads this

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {} == old(this.content()).Values
 
    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  }

  class MutableMapDafny<K(==),V(==)> extends MutableMapTrait<K,V> {
    var m: map<K,V>

    function content(): map<K, V> 
      reads this
    {
      m
    }

    constructor ()
      ensures this.content() == map[]
    {}

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
    {}

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
    {
      m.Keys
    }

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
    {}

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
    {}

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])
    {}

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
    {
      m[k]
    }

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {} == old(this.content()).Values
    {}

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
    {
      |m|
    }
  }
}

////////TESTS////////

method TestMutableMapDafny1() {
  var map := new MutableMapDafny<int, string>();
  map.Put(1, "one");
  map.Put(2, "two");
  var keys := map.Keys();
  var values := map.Values();
  var items := map.Items();
  var size := map.Size();
  assert keys == {1, 2};
  assert values == {"one", "two"};
  assert items == {(1, "one"), (2, "two")};
  assert size == 2;
}

method TestMutableMapDafny2() {
  var map := new MutableMapDafny<string, int>();
  map.Put("hello", 5);
  map.Put("world", 10);
  map.Remove("hello");
  var hasKey := map.HasKey("hello");
  var select := map.Select("world");
  var keys := map.Keys();
  var size := map.Size();
  assert hasKey == false;
  assert select == 10;
  assert keys == {"world"};
  assert size == 1;
}
