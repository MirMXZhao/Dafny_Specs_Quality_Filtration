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
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && (car !in old(carPark)) && (car !in old(reservedCarPark));
    ensures subscriptions == old(subscriptions) && weekend == old(weekend);
    {}

    // The method maintains the invariant that the number of available spaces availableSpaces is updated correctly
    // based on the current state of the car park and whether it is a weekend or not
    method checkAvailability() returns (availableSpaces: int)
    requires true
    modifies this
    ensures weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) + (reservedSpaces - old(|reservedCarPark|)) - badParkingBuffer;
    ensures !weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) - badParkingBuffer;
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend) && subscriptions == old(subscriptions);
    {}

    // The method maintains the invariant that if success is true, then the car parameter is added to the
    // subscriptions set. Otherwise, the subscriptions set is not modified
    method makeSubscription(car: string) returns (success: bool)
    requires true
    modifies this
    ensures success ==> old(|subscriptions|) < reservedSpaces && car !in old(subscriptions) && subscriptions == old(subscriptions) + {car};
    ensures !success ==> subscriptions == old(subscriptions) && (car in old(subscriptions) || old(|subscriptions|) >= reservedSpaces);
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend);
    {}

    method openReservedArea()
    requires true
    modifies this
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == true && subscriptions == old(subscriptions);
    {}

    method closeCarPark()
    requires true
    modifies this
    ensures carPark == {} && reservedCarPark == {} && subscriptions == {}
    ensures weekend == old(weekend);

    {}

    // The method maintains the invariant that if success is true, then the car parameter is added to the carPark
    // set and the number of cars in the carPark set is less than the number of normal spaces minus the bad parking
    // buffer. Otherwise, the carPark and reservedCarPark sets are not modified
    method enterCarPark(car: string) returns (success: bool)
    requires true
    modifies this;

    ensures success ==> (car !in old(carPark)) && (car !in old(reservedCarPark)) && (old(|carPark|) < normalSpaces - badParkingBuffer);
    ensures success ==> carPark == old(carPark) + {car};
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
    ensures !success ==> (car in old(carPark)) || (car in old(reservedCarPark) || (old(|carPark|) >= normalSpaces - badParkingBuffer));
    ensures subscriptions == old(subscriptions) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend);


    {}

    // The method maintains the invariant that if success is true, then the car parameter is added to the
    // reservedCarPark set and the number of cars in the reservedCarPark set is less than the number of
    // reserved spaces and either the weekend variable is true or the car parameter is in the subscriptions set.
    // Otherwise, the carPark and reservedCarPark sets are not modified
    method enterReservedCarPark(car: string) returns (success: bool)
    requires true
    modifies this;

    ensures success ==> (car !in old(carPark)) && (car !in old(reservedCarPark)) && (old(|reservedCarPark|) < reservedSpaces) && (car in subscriptions || weekend == true);
    ensures success ==> reservedCarPark == old(reservedCarPark) + {car};
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
    ensures !success ==> (car in old(carPark)) || (car in old(reservedCarPark) || (old(|reservedCarPark|) >= reservedSpaces) || (car !in subscriptions && weekend == false));
    ensures subscriptions == old(subscriptions) && carPark == old(carPark) && weekend == old(weekend);
    ensures weekend == old(weekend) && subscriptions == old(subscriptions);


  {}
}