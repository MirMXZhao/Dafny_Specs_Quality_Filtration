class Contador
{
    var valor: int;

    //construtor anônimo
    constructor ()
      ensures valor == 0
    {}

    //construtor com nome
    constructor Init(v:int)
      ensures valor == v
    {}

    method Incrementa()
      modifies this
      ensures valor == old(valor) + 1
    {}

    method Decrementa()
      modifies this
      ensures valor == old(valor) - 1
    {}

    method GetValor() returns (v:int)
      ensures v == valor
    {}
}

method Main()
{}
