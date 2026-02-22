/-
The goal here is to prove from scratch that for every integer n there exists a prime number greater than n

First you should get familiar with how prime numbers work in lean
-/
import Mathlib

--use loogle: https://loogle.lean-lang.org/ to find how/where primes are defined (annoyingly loogle is case sensitive)

#check Prime
#check Nat.Prime

--show that every integer ≥ 2 has a prime factor


--show that every integer >n has a prime larger than it. The classical argument is to find a prime factor of n!+1
