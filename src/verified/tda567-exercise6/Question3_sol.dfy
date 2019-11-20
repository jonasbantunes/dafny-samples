class Question3 {

  var x:int;
    
  method loop() returns (ret:int)
   requires x > 0;
   ensures ret == x * x;
  {
    var y:int := x;
    var z:int := 0;

    while (y > 0) 
     invariant y >= 0;
     invariant x * y + z == x * x;
     decreases y;
    {
       z := z + x;
       y := y - 1;
    }
 
    return z;
  }
}
