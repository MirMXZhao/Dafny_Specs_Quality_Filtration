class {:autocontracts} CarPark {
    const totalSpaces: nat := 10;
    const normalSpaces: nat:= 7;
    const reservedSpaces: nat := 3;
    const badParkingBuffer: int := 5;

    var weekend: bool;
    var subscriptions: set<string>;
    var carPark: set<string>;
    var reservedCarPark: set<string>;

    constructor()
    requires true
    ensures this.subscriptions == {} && this.carPark == {} && this.reservedCarPark == {} && this.weekend == false;
    {}

    // This predicate checks if the car park is in a valid state at all times.
    // It checks if the sets of cars in the car park and the reserved car park are disjoint and share no values,
    // the total number of cars in the car park is less than or equal to the total number of spaces in
    // the car park plus the bad parking buffer, the number of normal spaces plus reserved spaces is
    // equal to the total number of spaces, and the number of cars in the reserved car park is less than or equal
    // to the number of reserved spaces
    ghost predicate Valid()
    reads this
    {}

  // The method maintains the invariant that if success is true, then the car parameter is removed from either
  // the carPark or the reservedCarPark set. Otherwise, neither set is modified
  method leaveCarPark(car: string) returns (success: bool)
    requires true
    modifies this
    ensures success ==> (((car in old(carPark)) && carPark == old(carPark) - {car} && reservedCarPark == old(reservedCarPark)) || ((car in old(reservedCarPark)) && reservedCarPark == old(reservedCarPark) - {car} && carPark == old(carPark)));
    ensures success ==> (car !in carPark) && (car !in reservedCarPark);
    ensures !success ==> carPark == old(carPark) && reservedCarPark

////////TESTS////////

method TestLeaveCarPark1() {
  var carPark := new CarPark();
  carPark.carPark := {"car1", "car2"};
  carPark.reservedCarPark := {"car3"};
  var success := carPark.leaveCarPark("car1");
  assert success == true;
}

method TestLeaveCarPark2() {
  var carPark := new CarPark();
  carPark.carPark := {"car1", "car2"};
  carPark.reservedCarPark := {"car3"};
  var success := carPark.leaveCarPark("car4");
  assert success == false;
}
