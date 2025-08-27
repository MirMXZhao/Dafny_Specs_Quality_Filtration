datatype Valve = ON | OFF

class Pipe{}
class Tank
{} 

method checkRegulation(tank: Tank)
ensures (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)) 
|| (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3))
|| ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1))
modifies tank.pipe;
 {}

////////TESTS////////

method TestcheckRegulation1() {
  var pipe := new Pipe;
  pipe.v1 := ON;
  pipe.v2 := OFF;
  pipe.v3 := OFF;
  pipe.in_flowv1 := 3;
  pipe.in_flowv3 := 2;
  var tank := new Tank;
  tank.height := 12;
  tank.pipe := pipe;
  var old_v2 := tank.pipe.v2;
  checkRegulation(tank);
  assert tank.pipe.v1 == OFF && tank.pipe.v3 == ON && tank.pipe.v2 == old_v2;
}

method TestcheckRegulation2() {
  var pipe := new Pipe;
  pipe.v1 := ON;
  pipe.v2 := OFF;
  pipe.v3 := ON;
  pipe.in_flowv1 := 2;
  pipe.in_flowv3 := 3;
  var tank := new Tank;
  tank.height := 6;
  tank.pipe := pipe;
  var old_v3 := tank.pipe.v3;
  checkRegulation(tank);
  assert tank.pipe.v1 == OFF && tank.pipe.v2 == ON && tank.pipe.v3 == old_v3;
}
