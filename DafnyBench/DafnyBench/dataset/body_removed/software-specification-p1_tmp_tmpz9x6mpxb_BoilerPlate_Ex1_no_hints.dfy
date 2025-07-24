datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{}

// Ex 1
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
  requires |codes| > 0 || |trees| > 0
  ensures |deserialiseAux(codes, trees)| >= 0
{}

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
  requires |s| > 0
{}

// Ex 2
method testSerializeWithASingleLeaf()
{}

method testSerializeNullValues()
{}

method testSerializeWithAllElements()
{}

// Ex 3 

method testDeseraliseWithASingleLeaf() {}

method testDeserializeWithASingleNode()
{}

method testDeserialiseWithAllElements()
{}

// Ex 4 
lemma SerialiseLemma<V>(t: Tree<V>)
  ensures deserialise(serialise(t)) == [t]
{}


lemma DeserialisetAfterSerialiseLemma<T> (t : Tree<T>, cds : seq<Code<T>>, ts : seq<Tree<T>>) 
  ensures deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t])
  {}

