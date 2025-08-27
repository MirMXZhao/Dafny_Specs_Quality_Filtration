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

////////TESTS////////

method TestBinaryAddition1() {
  var s := new bool[10];
  var t := new bool[10];
  s[0] := true; s[1] := false; s[2] := true; s[3] := false; s[4] := true; s[5] := false; s[6] := true; s[7] := false; s[8] := true; s[9] := false;
  t[0] := false; t[1] := true; t[2] := false; t[3] := true; t[4] := false; t[5] := true; t[6] := false; t[7] := true; t[8] := false; t[9] := true;
  var sresult := BinaryAddition(s, t);
  assert sresult == [true, true, true, true, true, true, true, true, true, true];
}

method TestBinaryAddition2() {
  var s := new bool[10];
  var t := new bool[10];
  s[0] := false; s[1] := false; s[2] := false; s[3] := false; s[4] := false; s[5] := false; s[6] := false; s[7] := false; s[8] := false; s[9] := false;
  t[0] := true; t[1] := true; t[2] := false; t[3] := false; t[4] := false; t[5] := false; t[6] := false; t[7] := false; t[8] := false; t[9] := false;
  var sresult := BinaryAddition(s, t);
  assert sresult == [true, false, true, false, false, false, false, false, false, false];
}
