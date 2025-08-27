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