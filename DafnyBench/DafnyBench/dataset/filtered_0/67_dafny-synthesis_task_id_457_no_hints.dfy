method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{}