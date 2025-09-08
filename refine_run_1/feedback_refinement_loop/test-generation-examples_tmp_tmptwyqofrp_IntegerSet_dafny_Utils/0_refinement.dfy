module Utils {
  class Assertions<T> {
    // Assert methods terminate execution immediately on failure
    static method {:extern} assertEquals(expected : T, actual : T)
    requires expected == actual

    // Expect methods record failures and continue execution
    static method {:extern} expectEquals(expected : T, actual : T)
    ensures expected == actual

    // Assert methods terminate execution immediately on failure
    static method {:extern} assertTrue(condition : bool)
    requires condition

    // Expect methods record failures and continue execution
    static method {:extern} expectTrue(condition : bool)
    ensures condition
    
    // Assert methods terminate execution immediately on failure
    static method {:extern} assertFalse(condition : bool)
    requires !condition

    // Expect methods record failures and continue execution
    static method {:extern} expectFalse(condition : bool)
    ensures !condition
  }
}