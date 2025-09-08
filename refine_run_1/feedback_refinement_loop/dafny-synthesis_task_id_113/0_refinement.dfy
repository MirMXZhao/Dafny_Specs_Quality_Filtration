predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsAllDigitsString(s: string) returns (result: bool)
    requires s != null
    ensures |s| == 0 ==> result == false
    ensures |s| > 0 ==> (result <==> (forall i :: 0 <= i < |s| ==> IsDigit(s[i])))
{
    result := true;
    if |s| == 0 {
        result := false;
    } else {
        for i := 0 to |s|
            invariant 0 <= i <= |s|
            invariant result <==> (forall k :: 0 <= k < i ==> IsDigit(s[k]))
        {
            if !IsDigit(s[i]) {
                result := false;
                break;
            }
        }
    }
}