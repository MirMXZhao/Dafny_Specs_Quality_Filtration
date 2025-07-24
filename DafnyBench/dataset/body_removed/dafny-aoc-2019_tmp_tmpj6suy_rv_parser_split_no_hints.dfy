module Split {
    function splitHelper(s: string, separator: string, index: nat, sindex: nat, results: seq<string>): seq<seq<char>>
        requires index <= |s|
        requires sindex <= |s|
        requires sindex <= index
        // requires forall ss: string :: ss in results ==> NotContains(ss,separator)
        // ensures forall ss :: ss in splitHelper(s, separator, index, sindex, results) ==> NotContains(ss, separator)
    {}

    function split(s: string, separator: string): seq<string> 
        ensures split(s, separator) == splitHelper(s, separator, 0,0, [])
    {}

    predicate Contains(haystack: string, needle: string)
        // ensures !NotContainsThree(haystack, needle)
        ensures Contains(haystack, needle) <==> exists k :: 0 <= k <= |haystack| && needle <= haystack[k..] 
        ensures Contains(haystack, needle) <==> exists i :: 0 <= i <= |haystack| && (needle <= haystack[i..])
        ensures !Contains(haystack, needle) <==> forall i :: 0 <= i <= |haystack| ==> !(needle <= haystack[i..])
    {}

    function splitOnBreak(s: string): seq<string> {}

    function splitOnDoubleBreak(s: string): seq<string> {}
}
