method BinarySearch(a: array<int>, value: int) 
       returns (index: int)
   requires a != null && 0 <= a.Length;
   requires forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k];
   ensures 0 <= index ==> index < a.Length && a[index] == value;
   ensures 
       index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value;
{
   var low, high := 0, a.Length;
   while (low < high)
    invariant 0 <= low <= high <= a.Length;
    invariant 
      forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != value;
   {
      var mid := (low + high) / 2;
      if (a[mid] < value) {
         low := mid;
      }
      else if (value < a[mid]) {
         high := mid - 1;
      }
      else {
         return mid;
      }
   }
   return -1;
}