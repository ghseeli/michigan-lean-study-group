/-
The goal here is to prove from scratch that for every integer n there exists a prime number greater than n

First you should get familiar with how prime numbers work in lean
-/
import Mathlib

--use loogle: https://loogle.lean-lang.org/ to find how/where primes are defined (annoyingly loogle is case sensitive)

#check Prime
#check Nat.Prime 5
#check ne_zero_of_dvd_ne_zero

--show that every integer ≥ 2 has a prime factor
theorem every_int_has_a_prime_factor (n :ℕ) (h_ge2: n>1): ∃ (p : ℕ), (Nat.Prime p) ∧ (p ∣ n) :=by
  induction' n using Nat.strong_induction_on with m h_m
  have h_m_nonzero: m ≠ 0 :=by linarith
  · by_cases h: (Nat.Prime m)
    · use m
    rw[Nat.not_prime_iff_exists_dvd_ne] at h
    rcases h with ⟨d, hd1, hd2, hd3⟩
    specialize h_m d
    have h_p: ∃ (p: ℕ), (Nat.Prime p) ∧ (p ∣ d) :=by
      have h_d_nonzero: d ≠ 0 :=by
        apply ne_zero_of_dvd_ne_zero h_m_nonzero
        exact hd1
      apply h_m
      · refine Nat.lt_of_le_of_ne ?_ hd3
        apply Nat.divisor_le
        unfold Nat.divisors
        rw[Finset.mem_filter]
        constructor
        · rw[Finset.mem_Ico, Order.lt_add_one_iff]
          constructor
          · exact Nat.one_le_iff_ne_zero.mpr h_d_nonzero
          apply Nat.le_of_dvd
          exact pos_of_ne_zero h_m_nonzero
          exact hd1
        exact hd1
      cases d with
      | zero =>
        exfalso
        exact false_of_ne h_d_nonzero
      | succ d =>
        cases d with
        | zero =>
          exfalso
          exact false_of_ne hd2
        | succ d =>
          simp only [gt_iff_lt, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le]
    rcases h_p with ⟨p, h_p1, h_p2⟩
    use p
    constructor
    exact h_p1
    exact Nat.dvd_trans h_p2 hd1
    linarith


--short theorem I can apply
#check Nat.add_factorial_le_factorial_add 2
#check Nat.gcd _ _
#check dvd_gcd_iff
#check Nat.Coprime

--show that every integer >n has a prime larger than it. The classical argument is to find a prime factor of n!+1
theorem inifinite_primes (n :ℕ): ∃ (p : ℕ), (Nat.Prime p) ∧ (p > n) :=by
  have h_ge2: Nat.factorial (n+2)+1 > 1 :=by
    have h_easier_ge2: Nat.factorial (n+2) ≥ n+2 :=by
      apply Nat.self_le_factorial (n + 2)
    omega
  obtain hp := every_int_has_a_prime_factor (Nat.factorial (n+2) + 1) h_ge2
  rcases hp with ⟨p, hp1, hp2⟩
  use p
  constructor
  · exact hp1
  by_contra
  push_neg at this
  have h_p_div_gcd : p ∣ gcd p (Nat.factorial (n+2)+1) :=by
    apply Nat.dvd_gcd
    · exact Nat.dvd_refl p
    exact hp2
  have h_p_mid : p ∣ (Nat.factorial (n+2)) :=by
    refine Nat.dvd_factorial ?_ ?_
    · exact Nat.Prime.pos hp1
    exact Nat.le_add_right_of_le this
  have h_coprime: Nat.Coprime p (Nat.factorial (n+2)+1) :=by
    exact Nat.Coprime.coprime_dvd_left h_p_mid (by simp [Nat.Coprime])
  have h_gcd_comp: gcd p (Nat.factorial (n+2)+1) = 1 :=by
    exact Rat.natCast_eq_one_iff.mp (congrArg Nat.cast h_coprime)
  rw[h_gcd_comp] at h_p_div_gcd
  apply Nat.Prime.not_dvd_one at hp1
  exact hp1 h_p_div_gcd
