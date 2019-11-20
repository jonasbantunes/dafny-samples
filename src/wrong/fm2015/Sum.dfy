function sum(a: seq<int>): int
{
   if |a| == 0 then 0 else a[0] + sum(a[1..])
}

method SumIter(a: seq<int>) returns (s: int) 
ensures s == sum(a);
{
  s := 0;
  var i := 0;
  while (i < |a|)
  {
    s := s + a[i];
    i := i + 1;
  }
}
