class HashTable {
  
  // Open addressing Hashtable with linear probing as collision resolution.
  
  var hashtable:array<int>;
  var capacity:int;
  var size:int;	
	
  predicate Valid()
    reads this, hashtable;
  {
    hashtable != null && 
      0 <= size <= capacity && 
      capacity == hashtable.Length &&
      capacity > 0  
  }

  method Init(c:int)
    requires c > 0
    ensures Valid()
    ensures capacity == c && size == 0
    ensures forall i :: 0 <= i < hashtable.Length ==> hashtable[i] == 0
    ensures fresh(hashtable)
    modifies this
  {
    hashtable := new int[c]; 
    capacity := c;
    size := 0;
    
    forall (i | 0 <= i < hashtable.Length) {
      hashtable[i] := 0;
    }
  }
  
  function method hash_function(key:int):(int)
    requires Valid()
    ensures 0 <= hash_function(key) < hashtable.Length
    reads this, hashtable
  {
    var result:int := 0;
    
    if (key >= 0)
      then key % capacity
    else (key * -1) % capacity
  }

  method Add(val:int, key:int)
    requires Valid();
    requires val > 0;
    requires size < capacity;
    ensures Valid();
    ensures size == old(size) + 1;
    ensures exists j :: 0 <= j < size ==> hashtable[j] == val && forall k :: 0 <= k < size &&
      j != k ==> hashtable[k] == old(hashtable[k]);
    modifies hashtable, `size;
  {
    var i:int := hash_function(key);

    if (hashtable[i] == 0) {
	    hashtable[i] := val;
      size := size + 1;
	    return;
    }
	  else {
      var j:int := 0;
      
      while (hashtable[i] != 0 && j < capacity)
        invariant 0 <= j <= capacity;
        invariant 0 <= i < capacity;
        decreases capacity - j;
      {
        if (i == capacity-1) 
        {i := 0;}
        else {i := i + 1;}
          
          j := j + 1;
 	    }

      hashtable[i] := val;
      size := size + 1;        
    }
  }
}


