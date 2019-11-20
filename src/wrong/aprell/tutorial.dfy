// Exercise 0
method Max(a: int, b: int) returns (c: int)
    // ensures (a > b && c == a) || (a <= b && c == b)
    ensures a > b ==> c == a
    ensures a <= b ==> c == b
{
    if a > b { return a; }
    else { return b; }
}

// Exercise 1
method Testing()
{
    var a, b := -1, 2;
    var c := Max(a, b);
    assert b == c;
}

// Exercise 2
method Abs(x: int) returns (y: int)
    requires x < 0
    ensures 0 < y && y == -x
{
    return -x;
}

// Exercise 3
method Abs(x: int) returns (y: int)
    requires x == -1
    ensures 0 <= y
    ensures 0 <= x ==> x == y
    ensures x < 0 ==> y == -x
{
    y := x + 2;
}

method Abs2(x: int) returns (y: int)
    // Impossible
    ensures 0 <= y
    ensures 0 <= x ==> x == y
    ensures x < 0 ==> y == -x
{
    y := x + 1;
}

// Exercise 4
function max(a: int, b: int): int
{
    if a > b then a else b
}

method Testing() {
    assert max(1, 2) == 2;
    assert max(2, 1) == 2;
    assert max(-1, -1) == -1;
}

// Exercise 5
function method max(a: int, b: int): int
{
    if a > b then a else b
}

method Testing() {
    var a, b, c := max(1, 2), max(2, 1), max(-1, -1);
    assert a == 2;
    assert b == 2;
    assert c == -1;
}

// Exercise 6
function method abs(x: int): int
{
    if x < 0 then -x else x
}

method Abs(x: int) returns (y: int)
    ensures 0 <= y
    ensures y == abs(x)
{
    return abs(x);
}

// Exercise 7
method m(n: nat)
{
    var i: int := 0;
    while i < n
        invariant 0 <= i <= n + 2
    {
        i := i + 1;
    }
    // i >= n && i - 2 <= n
    assert i - 2 <= n <= i
}

// Exercise 8
method m(n: nat)
{
    var i: int := 0;
    while i != n
        invariant 0 <= i <= n
    {
        i := i + 1;
    }
    assert i == n;
}

function fib(n: nat): nat
{
    if n == 0 then 0
    else if n == 1 then 1
    else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
    ensures b == fib(n)
{
    if n == 0 { return 0; }
    var i: int := 1;
    var a := 0;
        b := 1;
    while i < n
        invariant 0 < i <= n
        invariant a == fib(i - 1)
        invariant b == fib(i)
    {
        a, b := b, a + b;
        i := i + 1;
    }
}

// Exercise 9
method ComputeFib(n: nat) returns (b: nat)
    ensures b == fib(n)
{
    if n == 0 { return 0; }
    var i: int := 1;
    var c := 1;
        b := 1;
    while i < n
        invariant 0 < i <= n
        invariant b == fib(i)
        invariant c == fib(i + 1)
    {
        b, c := c, b + c;
        i := i + 1;
    }
}

// Exercise 10
method ComputeFib(n: nat) returns (b: nat)
    ensures b == fib(n)
{
    var i: int := 0;
    var a := 1;
        b := 0;
    while i < n
        invariant 0 <= i <= n
        invariant i == 0 ==> a == fib(1)
        invariant i > 0 ==> a == fib(i - 1)
        invariant b == fib(i)
    {
        a, b := b, a + b;
        i := i + 1;
    }
}

// Exercise 11
method m()
{
    var i, n := 0, 20;
    while i != n
        invariant 0 <= n - i
        decreases n - i
    {
        i := i + 1;
    }
}

// Exercise 12
method FindMax(a: array<int>) returns (i: int)
    requires a.Length > 0
    ensures 0 <= i ==> i < a.Length && forall j :: 0 <= j < a.Length ==> a[j] <= a[i]
{
    var j := 1;
        i := 0;
    while j < a.Length
       invariant 0 <= j <= a.Length
       invariant 0 <= i < j
       invariant forall k :: 0 <= k < j ==> a[k] <= a[i]
    {
        if a[j] > a[i] { i := j; }
        j := j + 1;
    }
}

// Exercise 13
predicate sorted(a: array<int>)
    reads a
{
    forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

// Exercise 14
predicate sorted(a: array?<int>)
    reads a
{
    forall j, k :: a != null && 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// Exercise 15
method BinarySearch(a: array<int>, value: int) returns (index: int)
    requires 0 <= a.Length && sorted(a)
    ensures 0 <= index ==> index < a.Length && a[index] == value
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
    var low, high := 0, a.Length;
    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant forall i ::
            0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
    {
        var mid := low + (high - low) / 2;
        if a[mid] < value
        {
            low := mid + 1;
            // low := mid
            // => Error: cannot prove termination
        }
        else if value < a[mid]
        {
            high := mid;
            // high := mid - 1;
            // => Error: loop invariant violation
        }
        else
        {
            return mid;
        }
    }
    return -1;
}
