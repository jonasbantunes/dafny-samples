class Counter {

  var value : int ;

  // this predicate can be seen as an object invariant, i.e. the
  // properties that the object must always satisfy
  predicate valid()
    reads this;
  {
    value >= 0
  }
  
  constructor init()
    ensures value == 0;
    ensures valid();
    modifies `value;
  {
    value := 0 ;
  }
  
  method getValue() returns (x:int)
    ensures x == value;
    // since the object is not modified, no need to ensure valid()
  {
    x := value ;
  }
  
  method inc()
    requires valid();
    ensures value == old(value) + 1;
    ensures valid();
    modifies `value;
  {
    value := value + 1;
  }
  
  method dec()
    requires valid();
    requires value > 0; // without this pre-condition, the post-condition could be violated
    ensures value == old(value) - 1;
    ensures valid();
    modifies `value;
  { 
    value := value - 1 ;
  }
  
  method Main ()
  {
   var count := new Counter.init() ;
   count.inc();
   count.inc();
   count.dec();
   count.inc();
   var aux : int := count.getValue();
   assert (aux == 2) ;
  }
}
