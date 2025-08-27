class {:autocontracts} Graph<T(==)> {
   var V: set<T>; 
   var E: set<(T, T)>; 

   ghost predicate Valid() {
       forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1
   } 

   constructor ()
     ensures V == {} && E == {}
     {}

   method addVertex(v: T)
     requires v !in V
     ensures E == old(E) && V == old(V) + {v}
     {}

   method addEdge(u: T, v: T)
     requires u in V && v in V && (u, v) !in E && u != v
     ensures V == old(V) && E == old(E) + {(u, v)} 
     {}

   function getAdj(v: T): set<T>
     requires v in V
     {} 

   method removeVertex(v: T)
     requires v in V
     ensures V == old(V) - {v}
     ensures E == set e | e in old(E) && e.0 != v && e.1 != v 
     {}

    // Collapses a subset C of vertices to a single vertex v (belonging to C).
    // All vertices in C are removed from the graph, except v.  
    // Edges that connect vertices in C are removed from the graph.  
    // In all other edges, vertices belonging to C are replaced by v.
    method collapseVertices(C: set<T>, v: T)
      requires v in C && C <= V 
      ensures V == old(V) - C + {v}
      ensures E == set e | e in old(E) && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1)
  {}    
}

////////TESTS////////

method TestCollapseVertices1() {
  var g := new Graph<int>();
  g.addVertex(1);
  g.addVertex(2);
  g.addVertex(3);
  g.addVertex(4);
  g.addEdge(1, 2);
  g.addEdge(2, 3);
  g.addEdge(3, 4);
  g.collapseVertices({1, 2}, 1);
  assert g.V == {1, 3, 4};
  assert g.E == {(1, 3), (3, 4)};
}

method TestCollapseVertices2() {
  var g := new Graph<int>();
  g.addVertex(5);
  g.addVertex(6);
  g.addVertex(7);
  g.addEdge(5, 6);
  g.addEdge(6, 7);
  g.collapseVertices({6, 7}, 7);
  assert g.V == {5, 7};
  assert g.E == {(5, 7)};
}
