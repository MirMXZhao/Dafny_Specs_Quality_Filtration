function ArrayToBv10(arr: array<bool>): bv10
    reads arr
    requires arr.Length == 10
{}

function ArrayToBv10Helper(arr: array<bool>, index: nat): bv10
    reads arr
    requires arr.Length == 10
    requires 0 <= index < arr.Length
    decreases index
    ensures forall i :: 0 <= i < index ==> ((ArrayToBv10Helper(arr, i) >> i) & 1) == (if arr
        [i] then 1 else 0)
{}

method ArrayToSequence(arr: array<bool>) returns (res: seq<bool>)
    ensures |res| == arr.Length
    ensures forall k :: 0 <= k < arr.Length ==> res[k] == arr[k]
{}

function isBitSet(x: bv10, bitIndex: nat): bool
    requires bitIndex < 10
    ensures isBitSet(x, bitIndex) <==> (x & (1 << bitIndex)) != 0
{}

function Bv10ToSeq(x: bv10): seq<bool>
    ensures |Bv10ToSeq(x)| == 10
    ensures forall i: nat :: 0 <= i < 10 ==> Bv10ToSeq(x)[i] == isBitSet(x, i)
{}

function BoolToInt(a: bool): int {}

function XOR(a: bool, b: bool): bool {}

function BitAddition(s: array<bool>, t: array<bool>): seq<bool>
    reads s
    reads t
    requires s.Length == 10 && t.Length == 10
{}

method BinaryAddition(s: array<bool>, t: array<bool>) returns (sresult: seq<bool>)
    requires s.Length == 10 && t.Length == 10
    ensures |sresult| == 10
    ensures forall i :: 0 <= i && i < |sresult| ==> sresult[i] == ((s[i] != t[i]) != (i > 0
                    && ((s[i-1] || t[i-1]) && !(sresult[i-1] && (s[i-1] != t[i-1])))))
    ensures BitAddition(s, t) == sresult
{}