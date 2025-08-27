datatype HAlign = Left | Center | Right
datatype VAlign = Top | Middle | Bottom
datatype TextAlign = TextAlign(hAlign:HAlign, vAlign:VAlign)

datatype GraphicsAlign = Square | Round

datatype PageElement = Text(t:TextAlign) | Graphics(g:GraphicsAlign)

lemma NumPageElements()
  ensures exists eltSet:set<HAlign> :: |eltSet| == 3
  ensures forall eltSet:set<HAlign> :: |eltSet| <= 3
{}

lemma subsetCardinality<T>(a:set<T>, b:set<T>)
  requires a <= b
  ensures |a| <= |b|
{}

////////TESTS////////

method TestNumPageElements1() {
  NumPageElements();
  var eltSet := {Left, Center, Right};
  assert |eltSet| == 3;
}

method TestNumPageElements2() {
  NumPageElements();
  var eltSet := {Left, Center};
  assert |eltSet| <= 3;
}
