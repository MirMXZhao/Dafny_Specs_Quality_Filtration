class Grinder { 
	ghost var hasBeans: bool 
    ghost var Repr: set<object>

	ghost predicate Valid() 
		reads this, Repr
        ensures Valid() ==> this in Repr
		
	constructor() 
		ensures Valid() && fresh(Repr) && !hasBeans

    function Ready(): bool 
		requires Valid() 
		reads Repr
		ensures Ready() == hasBeans 

	method AddBeans() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && hasBeans && fresh(Repr-old(Repr))

	method Grind() 
		requires Valid() && hasBeans 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr))
}

class WaterTank { 
	ghost var waterLevel: nat
    ghost var Repr: set<object>

	ghost predicate Valid() 			 
		reads this, Repr 		
        ensures Valid() ==> this in Repr

	constructor() 				 
		ensures Valid() && fresh(Repr) && waterLevel == 0

    function Level(): nat 
		requires Valid()
		reads Repr
		ensures Level() == waterLevel

	method Fill() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == 10 

	method Use() 
		requires Valid() && waterLevel != 0 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == old(Level()) - 1  
}

class CoffeeMaker { 	
	var g: Grinder 	
	var w: WaterTank
	ghost var ready: bool
	ghost var Repr: set<object>

	ghost predicate Valid() 
		reads this, Repr 
        ensures Valid() ==> this in Repr
	{}

    constructor() 
		ensures Valid() && fresh(Repr)
	{}

    predicate Ready() 
		requires Valid() 
		reads Repr
		ensures Ready() == ready
	{}

    method Restock() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && Ready() && fresh(Repr - old(Repr))
	{} 

    method Dispense()
		requires Valid() && Ready() 
		modifies Repr 
		ensures Valid() && fresh(Repr - old(Repr))
	{}
}

method CoffeeTestHarness() {}


