ghost function Hash(s:string):int {}

ghost function SumChars(s: string):int {}
class CheckSumCalculator{
    var data: string
    var cs:int

    ghost predicate Valid()
        reads this
    {
        cs == Hash(data)
    }

    constructor ()
        ensures Valid() && data == ""
    {}

    method Append(d:string)
        requires Valid()
        modifies this
        ensures Valid() && data == old(data) + d
    {}

    function GetData(): string
        requires Valid()
        reads this
        ensures Hash(GetData()) == Checksum()
    {
        data
    }

    function Checksum(): int 
        requires Valid()
        reads this 
        ensures Checksum() == Hash(data)
    {
        cs
    }
}

////////TESTS////////

method TestHash1() {
  var result := Hash("hello");
  assert result == Hash("hello");
}

method TestHash2() {
  var result := Hash("");
  assert result == Hash("");
}

method TestSumChars1() {
  var result := SumChars("abc");
  assert result == SumChars("abc");
}

method TestSumChars2() {
  var result := SumChars("");
  assert result == SumChars("");
}

method TestCheckSumCalculatorConstructor1() {
  var calc := new CheckSumCalculator();
  assert calc.Valid();
  assert calc.data == "";
}

method TestCheckSumCalculatorConstructor2() {
  var calc := new CheckSumCalculator();
  assert calc.Valid();
  assert calc.data == "";
}

method TestAppend1() {
  var calc := new CheckSumCalculator();
  var oldData := calc.data;
  calc.Append("test");
  assert calc.Valid();
  assert calc.data == oldData + "test";
}

method TestAppend2() {
  var calc := new CheckSumCalculator();
  var oldData := calc.data;
  calc.Append("");
  assert calc.Valid();
  assert calc.data == oldData + "";
}

method TestGetData1() {
  var calc := new CheckSumCalculator();
  var result := calc.GetData();
  assert result == "";
  assert Hash(result) == calc.Checksum();
}

method TestGetData2() {
  var calc := new CheckSumCalculator();
  calc.Append("hello");
  var result := calc.GetData();
  assert result == "hello";
  assert Hash(result) == calc.Checksum();
}

method TestChecksum1() {
  var calc := new CheckSumCalculator();
  var result := calc.Checksum();
  assert result == Hash(calc.data);
}

method TestChecksum2() {
  var calc := new CheckSumCalculator();
  calc.Append("world");
  var result := calc.Checksum();
  assert result == Hash(calc.data);
}
