
method Q1(){
     var a := new int[6];
     a[0],a[1],a[2],a[3],a[4],a[5] := 1,0,0,0,1,1;
     var b := new int[3];
     b[0],b[1],b[2] := 1,0,1; 
     
     var j,k := 1,3;
     var p,r := 4,5;

     // a) All elements in the range a[j..k] are 0.
     assert forall i : int :: j <= i <= k ==> a[i] == 0;

     // b) All zeros in a occur in the interval a[j..k].
     assert forall i : int :: 0 <= i < a.Length && a[i] == 0 ==> j <= i <= k;
                                     
     // c) It is *not* the case that all ones of a[0...n-1] occur in the interval in a[p..r]  
     assert !(forall i : int :: 0 <= i < a.Length && a[i] == 1 ==> p <= i <= r);
     assert exists i : int ::  0 <= i < a.Length && a[i] == 1 && (i < p || i > r);                            
                 
     //d) a[0..n-1] contains at least two zeros.
     assert exists i1,i2 : int :: 0 <= i1 < a.Length && 0 <= i2 < a.Length && i1 != i2 && a[i1] == 0 && a[i2] == 0;
     // alternatively:
     assert exists i1,i2 : int :: 0 <= i1 < i2 < a.Length && a[i1] == 0 && a[i2] == 0;
     
     //e) b[0..n-1] contains at most two zeros. Note that this is trivially true if the lenght is less than 3.
     assert b.Length < 3 || (forall i1,i2,i3 : int :: 0 <= i1 < i2 < i3 < b.Length ==> b[i1] != 0 || b[i2] != 0 || b[i3] != 0);     
     
}
