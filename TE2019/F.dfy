function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}
//An algorithm to calculate F(n) iteratively is described by the following method in Dafny:

method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{
  var a, b, c := 0, 1, 2;
  var i := 0;
  assert a == F(0) && b == F(1) && c == F(2); //P => I
  while i < n 
  decreases n - i
  invariant 0 <= i <= n
  invariant a == F(i) && b == F(i + 1) && c == F(i + 2)
  {
    a, b, c := b, c, a + c;        
    i := i + 1;
	assert 0 <= i <= n && a == F(i) && b == F(i + 1) && c == F(i + 2);
  }
  res := a;
  assert (a == F(i) && b == F(i + 1) && c == F(i + 2)) ==> res == F(n);//I ^ ~C => Q
}