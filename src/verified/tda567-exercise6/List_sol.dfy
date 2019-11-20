class List {

  // container for the list's elements
  var a: array<int>;
  // size of the list
  var size: nat;

  predicate Valid()
    reads a, this
  {
    a != null &&
      size >= 0 &&
      size <= a.Length &&
      0 < a.Length 
  }

  constructor init(len : int)
    requires len > 0
    ensures Valid()
    ensures fresh(a)
    ensures size == 0
    ensures a.Length == len
    modifies this
  {
    a := new int[len];
    size := 0;
  }

  method snoc(e : int)
    requires Valid() && size < a.Length
    ensures Valid()
    ensures size == old(size) + 1
    ensures a[size - 1] == e
    ensures forall i :: 0 <= i < old(size) ==> a[i] == old(a[i])
    modifies a, `size
  {
    a[size] := e;    
    size := size + 1;    
  }

  method cons(val : int)
    requires Valid() && size < a.Length
    ensures Valid()
    ensures size == old(size) + 1
    ensures forall i :: 1 <= i <= old(size) ==> a[i] == old(a[i-1])
    ensures a[0] == val
    modifies a, `size
  {      
    var i:int := size;
    while (i > 0) 
      invariant 0 <= i <= size ;
      invariant forall j :: 0 <= j < i ==> a[j] == old(a[j]) ;
      invariant forall j :: i < j <= size ==> a[j] == old(a[j-1]) ;
      decreases i;
      modifies a;
    {       
      a[i] := a[i-1];       
      i := i - 1 ;
    }
    a[0] := val;
    size := size + 1;
  }

  method tail()    
    requires Valid() && size > 0
    ensures Valid()
    ensures size == old(size) - 1
    ensures forall i :: 0 <= i < size-1 ==> a[i] == old(a[i+1])
    modifies `size, a
  { 
    var i:int := 0;
    while (i < size-1) 
      invariant 0 <= i < size ;
      invariant forall j :: 0 <= j < i ==> a[j] == old(a[j+1]) ;
      invariant forall j :: i < j < size ==> a[j] == old(a[j]) ;
      decreases size - i;
      modifies a;
    {       
      a[i] := a[i + 1];       
      i := i + 1;
    }
    size := size - 1;
  }
  
  method head() returns (h : int)
    requires Valid() && size > 0
    ensures h == a[0] 
  {
    h := a[0] ;
  }
}
