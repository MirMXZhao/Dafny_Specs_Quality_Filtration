module Utils {
  class Assertions<T> {
    static method {:extern} assertEquals(expected : T, actual : T)
    requires expected == actual

    static method {:extern} expectEquals(expected : T, actual : T)
    requires expected == actual
    ensures expected == actual

    static method {:extern} assertTrue(condition : bool)
    requires condition

    static method {:extern} expectTrue(condition : bool)
    requires condition
    ensures condition
    
    static method {:extern} assertFalse(condition : bool)
    requires !condition

    static method {:extern} expectFalse(condition : bool)
    requires !condition
    ensures !condition
  }
}