//#title IsPrimeSpec I
//#desc Basic specification.
// Implement a predicate that tells whether a natural number is prime.

/*{*/
// function IsPrimeSpec
/*}*/
ghost predicate IsPrimeSpec(candidate:nat)
{
  /*{*/
    candidate > 1 && (forall d: nat :: d > 1 && d < candidate ==> candidate % d != 0)
  /*}*/
}

// illustrate IsPrimeSpec on a few examples (note that the verifier is able to
// check these only with some help to find divisors for non-prime numbers)
lemma ConstantObligations()
  ensures !IsPrimeSpec(0)
  ensures !IsPrimeSpec(1)
  ensures IsPrimeSpec(2)
  ensures IsPrimeSpec(3)
  ensures !IsPrimeSpec(4)
  ensures !IsPrimeSpec(6)
  ensures IsPrimeSpec(7)
  ensures !IsPrimeSpec(9)
{
  /*{*/
  assert(4 % 2 == 0);
  assert(6 % 2 == 0);
  assert(9 % 3 == 0);
  /*}*/
}

lemma CompositeIsntPrime(p: nat)
  requires 1 < p
  ensures !IsPrimeSpec(p*66)
{
  /*{*/
  assert(p*66 % 66 == 0);
  /*}*/
}
