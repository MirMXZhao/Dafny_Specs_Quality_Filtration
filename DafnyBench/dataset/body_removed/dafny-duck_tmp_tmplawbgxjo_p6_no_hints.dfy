//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {}

function FilterVowels(xs: seq<char>): seq<char>
{}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{}
