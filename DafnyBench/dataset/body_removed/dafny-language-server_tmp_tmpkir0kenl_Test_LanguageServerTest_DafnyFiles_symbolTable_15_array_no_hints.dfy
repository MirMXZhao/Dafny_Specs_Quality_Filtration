method Main() {}

method foo (s: seq<int>)
requires |s| > 1
{
    print s[1];
}
