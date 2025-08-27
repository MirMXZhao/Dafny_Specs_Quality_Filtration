// RUN: /nologo /rlimit:10000000 /noNLarith

abstract module Interface {}

abstract module Mod {
    import A : Interface
    method m() {}
}

module Implementation refines Interface {}

module Mod2 refines Mod {}

method Main() {
    Mod2.m();
}

