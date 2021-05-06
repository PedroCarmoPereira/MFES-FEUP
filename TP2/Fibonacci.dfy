
/*

Function vs Method

	Functions: simple expressions, max one line

	Methods: functions in other prog langs

*/
function fib(n : nat ) : nat
  decreases n
{
    if n < 2 then n else fib(n - 2) + fib(n - 1)
}

method computeFib (n : nat) returns (x : nat)
requires n >= 0
ensures x == fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    while  i < n 
	decreases n-i
	invariant 0 <= i <= n && x == fib(i) && y == fib(i+1)
    {
        x, y := y, x + y; // multiple assignment
        i := i + 1;
    }
}
