method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    found := false;
    c := 'a';
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant !found ==> (forall k, l :: 0 <= k < l < i && s[k] == s[l] ==> false)
        invariant found ==> exists p, q :: 0 <= p < q < i && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
    {
        var j := i + 1;
        while j < |s|
            invariant i + 1 <= j <= |s|
            invariant !found ==> (forall l :: i + 1 <= l < j ==> s[i] != s[l])
            invariant found ==> exists p, q :: 0 <= p < q <= i && s[p] == s[q] && s[p] == c && (forall k, l :: 0 <= k < l < q && s[k] == s[l] ==> k >= p)
        {
            if s[i] == s[j] {
                found := true;
                c := s[i];
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

method TestFindFirstRepeatedChar1() {
  var s := "abccba";
  var found, c := FindFirstRepeatedChar(s);
  assert found == true;
  assert c == 'c';
}

method TestFindFirstRepeatedChar2() {
  var s := "abcdef";
  var found, c := FindFirstRepeatedChar(s);
  assert found == false;
  assert c == 'a';
}