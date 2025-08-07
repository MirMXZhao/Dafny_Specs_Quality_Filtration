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

////////TESTS////////

method TestGrinder1() {
  var grinder := new Grinder();
  assert grinder.Valid();
  assert !grinder.hasBeans;
  assert !grinder.Ready();
}

method TestGrinder2() {
  var grinder := new Grinder();
  grinder.AddBeans();
  assert grinder.Valid();
  assert grinder.hasBeans;
  assert grinder.Ready();
}

method TestGrinder3() {
  var grinder := new Grinder();
  grinder.AddBeans();
  grinder.Grind();
  assert grinder.Valid();
}

method TestWaterTank1() {
  var tank := new WaterTank();
  assert tank.Valid();
  assert tank.waterLevel == 0;
  assert tank.Level() == 0;
}

method TestWaterTank2() {
  var tank := new WaterTank();
  tank.Fill();
  assert tank.Valid();
  assert tank.waterLevel == 10;
  assert tank.Level() == 10;
}

method TestWaterTank3() {
  var tank := new WaterTank();
  tank.Fill();
  tank.Use();
  assert tank.Valid();
  assert tank.waterLevel == 9;
  assert tank.Level() == 9;
}

method TestCoffeeMaker1() {
  var maker := new CoffeeMaker();
  assert maker.Valid();
}

method TestCoffeeMaker2() {
  var maker := new CoffeeMaker();
  maker.Restock();
  assert maker.Valid();
  assert maker.Ready();
}

method TestCoffeeMaker3() {
  var maker := new CoffeeMaker();
  maker.Restock();
  maker.Dispense();
  assert maker.Valid();
}
