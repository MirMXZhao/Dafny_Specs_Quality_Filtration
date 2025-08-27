class LFUCache {

    var capacity : int;
    var cacheMap : map<int, (int, int)>;

    constructor(capacity: int)
      requires capacity > 0;
      ensures Valid();
    {}

    predicate Valid()
      reads this;
    {} 

    method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
    {}

    method get(key: int) returns (value: int)
      requires Valid();
      modifies this;
      ensures Valid();
      ensures key !in cacheMap ==> value == -1;
      ensures forall e :: e in old(cacheMap) <==> e in cacheMap;
      ensures forall e :: e in old(cacheMap) ==> (old(cacheMap[e].0) == cacheMap[e].0);
      ensures key in cacheMap ==> value == cacheMap[key].0 && old(cacheMap[key].1) == cacheMap[key].1-1;
    {}
    
    
     method put(key: int, value: int)
        requires Valid();
        requires value > 0;
        modifies this
        ensures Valid();
       
     {}
 }

////////TESTS////////

method TestLFUCacheGet1() {
  var cache := new LFUCache(2);
  cache.cacheMap := map[1 := (10, 1), 2 := (20, 2)];
  var value := cache.get(1);
  assert value == 10;
}

method TestLFUCacheGet2() {
  var cache := new LFUCache(3);
  cache.cacheMap := map[5 := (50, 3)];
  var value := cache.get(7);
  assert value == -1;
}
