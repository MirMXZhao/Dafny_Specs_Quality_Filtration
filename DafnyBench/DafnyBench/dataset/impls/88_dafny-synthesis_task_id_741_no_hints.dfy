method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{
    if |s| <= 1 {
        result := true;
        return;
    }
    
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] == s[0]
    {
        if s[i] != s[0] {
            result := false;
            return;
        }
        i := i + 1;
    }
    result := true;
}

method TestAllCharactersSame1() {
  var result := AllCharactersSame("aaaa");
  assert result == true;
}

method TestAllCharactersSame2() {
  var result := AllCharactersSame("abcd");
  assert result == false;
}