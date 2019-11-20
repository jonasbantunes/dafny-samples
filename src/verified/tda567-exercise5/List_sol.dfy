class List {

  // container for the list's elements
  var a: array<int>;
  // size of the list
  var size: nat;

  predicate Valid()
  reads a, this;
  {
    a != null &&
    size <= a.Length &&
    0 < a.Length && size >= 0 
  }

  constructor init(len:int)
  requires len > 0 ;
  ensures Valid();
  ensures fresh(a);
  ensures size == 0;
  ensures a.Length == len ;
  modifies this;    
  {
    a := new int[len];
    size := 0;
  }

  method snoc(e: int)
    requires Valid() && size < a.Length ;
    ensures Valid();        
    ensures size == old(size) + 1;
    ensures a[old(size)] == e ;   
    ensures forall i :: 0 <= i < old(size) ==> a[i] == old(a[i])
    modifies a, `size;    
  {
    a[size] := e;    
    size := size + 1;    
  }

  method tail()    
    requires Valid() && size > 0;
    ensures Valid();    
    ensures size == old(size) - 1 ;
    ensures forall i :: 0 <= i < size-1 ==> a[i] == old(a[i+1]) ;
    modifies `size, a;
  {    
    forall (i | 0 <= i < size-1 ) {
      a[i] := a[i + 1];  
    }
    size := size - 1;
  }
  
  method head() returns (h:int)
  requires Valid() && size > 0;
  ensures Valid();
  ensures h == a[0] ; 
  {
    h := a[0] ;
  }
  
  method Main() 
  {
    var list := new List.init(4);
    var aux : int;  
    
    list.snoc(2);
    aux := list.head();
    assert (aux == 2) ;    
    
    list.snoc(3);    
    list.snoc(4);
    aux := list.head();    
    assert (aux == 2) ;
    
    list.tail() ;
    aux := list.head();
    assert aux == 3 ;
  }
}
