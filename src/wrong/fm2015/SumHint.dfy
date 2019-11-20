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
    invariant 0 <= i <= |a|
    invariant s == sum(a[0..i])
  {
    DistributiveLemma(a[0..i], [a[i]]);
    s := s + a[i];
    i := i + 1;
  }
}

lemma DistributiveLemma(a: seq<int>, b: seq<int>)
   ensures sum(a + b) == sum(a) + sum(b)
{
   if a == []
   {
      assert a + b == b;
   }
   else
   {
      DistributiveLemma(a[1..], b);
      assert a + b == [a[0]] + (a[1..] + b);
   }
}
