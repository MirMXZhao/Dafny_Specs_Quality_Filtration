ghost function Hash(s:string):int {}

ghost function SumChars(s: string):int {}
class CheckSumCalculator{
    var data: string
    var cs:int

    ghost predicate Valid()
        reads this
    {}

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

method Main() {}
