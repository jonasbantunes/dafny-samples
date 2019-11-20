method Division(x : int, y : int) returns (q : int, r : int)
  requires x >= 0
  requires y > 0
  ensures q * y + r == x
  ensures 0 <= r < y; 
{
  q := 0;
  r := x;
  while (r >= y) 
    invariant q * y + r == x
    invariant r >= 0;
    decreases r;
  {
    r := r - y;
    q := q + 1;
  }
}
