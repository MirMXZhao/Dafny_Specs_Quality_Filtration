// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class SumOfCubes {
  static function SumEmUp(n: int, m: int): int
    requires 0 <= n && n <= m;
  {}

  static method Socu(n: int, m: int) returns (r: int)
    requires 0 <= n && n <= m;
    ensures r == SumEmUp(n, m);
  {}

  static method SocuFromZero(k: int) returns (r: int)
    requires 0 <= k;
    ensures r == SumEmUp(0, k);
  {}

  ghost static method Lemma0(n: int, m: int)
    requires 0 <= n && n <= m;
    ensures SumEmUp(n, m) == SumEmUp(0, m) - SumEmUp(0, n);
  {}

  static function GSum(k: int): int
    requires 0 <= k;
  {}

  static method Gauss(k: int) returns (r: int)
    requires 0 <= k;
    ensures r == GSum(k);
  {}

  ghost static method Lemma1(k: int)
    requires 0 <= k;
    ensures SumEmUp(0, k) == GSum(k) * GSum(k);
  {}

  ghost static method Lemma2(k: int)
    requires 0 <= k;
    ensures 2 * GSum(k) == k * (k - 1);
  {}

  static function SumEmDown(n: int, m: int): int
    requires 0 <= n && n <= m;
  {}

  ghost static method Lemma3(n: int, m: int)
    requires 0 <= n && n <= m;
    ensures SumEmUp(n, m) == SumEmDown(n, m);
  {}
}



method TestSocu1() {
  var r := SumOfCubes.Socu(2, 5);
  assert r == SumOfCubes.SumEmUp(2, 5);
}

method TestSocu2() {
  var r := SumOfCubes.Socu(0, 3);
  assert r == SumOfCubes.SumEmUp(0, 3);
}

method TestSocuFromZero1() {
  var r := SumOfCubes.SocuFromZero(4);
  assert r == SumOfCubes.SumEmUp(0, 4);
}

method TestSocuFromZero2() {
  var r := SumOfCubes.SocuFromZero(0);
  assert r == SumOfCubes.SumEmUp(0, 0);
}

method TestGauss1() {
  var r := SumOfCubes.Gauss(5);
  assert r == SumOfCubes.GSum(5);
}

method TestGauss2() {
  var r := SumOfCubes.Gauss(1);
  assert r == SumOfCubes.GSum(1);
}
