method Add(x: int, y: int) returns (r: int)
  requires y >= 0
  ensures r == x + y
{
  r := x;
  var n := y;
  while n != 0
    invariant 
      0 <= n &&
      r == x + y - n
  {
    r := r + 1;
    n := n - 1;
  }
}