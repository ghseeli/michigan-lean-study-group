import Mathlib.Tactic
/-!
# lean_lec_feb9

Scratchpad / lecture file for Feb 9.
-/



/-Logistics
## 1. Discuss goals for the study group

* Check the proof of the infinitude of primes
* Learn enough to be able to tell if interested in trying to formalize anything specific in work and how to do that
* Developing tools for automating proofs / dealing with technical details
* How does formal verification actually work?
*

## 2. Next few mini-lectures
ideally we have some formal proof, type theory, theory heavy lectures
* speaker for type theory?
* speaker for Curry-Howard correspondence
* TODO: Resend links to mailing list
-/

/-
## 3. Natural Numbers Game Takeaways
Fun exercises, but somewhat painful to do.
Mimics working with lean but feeds you the important tactics/theorems instead of you looking them up.

Also there are several other games on that site.

Biggest takeaway
## TACTICS ##
A *goal* is what Lean is asking you to prove.

These tactics are “goal finishers” or “goal shapers”:
-- * `rfl` closes goals that are true by definitional equality (the two sides are literally the same after unfolding). This tactic is done automatically in VS code??


These tactics are “goal finishers” or “goal shapers”:
* `rfl` closes goals that are true by definitional equality (the two sides are literally the same after unfolding).
* `exact h` closes the goal if `h` is already a proof of it.
* `symm` flips an equality goal `a = b` into `b = a` (or flips an equality hypothesis with `symm at h`).
* `left` / `right` choose a side of an `Or` goal.
* `tauto` is a propositional logic solver (mathlib tactic).
-/



/-The rewrite tactic `rw` replaces occurrences of the left-hand side of an equation
with the right-hand side.

Key patterns:
* `rw [h]` rewrites in the goal.
* `rw [h] at hx` rewrites inside a hypothesis `hx`.
* `rw [h] at *` rewrites in *every* hypothesis and the goal.
* `rw [← h]` rewrites *backwards* (right-to-left).

Similarly the `apply` tactic a goal of B with a hypothesis of the form

    A → B

into the goal A.
-/

/-The `induction` tactic and `cases` tactics let us use standard math arguements
-/

/-
other helpful tactics: `simp`

## 4. Caveats for the natural numbers game
a lot of the time things are easier in lean because a lot of the work has already been done. For instance consider the below proof:

for instance the tactic
* `simp`,
* `ring` which checks if two expressions are equal in general rings,
* `omega` which tries to prove your inequality over the integers,
* `linarith` which tries to prove you inequlaities over fields
-/

def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => 2 * n + 1 + f n

#check f

#eval f 0
#eval f 1
#eval f 2
#eval f 3

/-
A digression (skippable) to answer some questions.

Just as there is a difference between considering a single natural number n ∈ ℕ versus the collection ℕ,
there is a difference between a proof of a proposition and the proposition itself.
A theorem is an /instance/ of an object whose type is given by the proposition.
The proposition itself is of type `Prop`.
-/

-- A theorem that is obviously false
def hi : ∀ n, n+1 = 2 := by sorry -- same as theorem hi : ∀ n, n+1 = 2 := by sorry
#check hi -- hi is an object of type ∀ n, n+1 = 2
-- The proposition that is the type of the theorem
def hi_prop := ∀ n, n+1 = 2
#check hi_prop -- hi_prop is of `Prop` type

theorem f_eq_square : ∀ n, f n = n^2 := by
  intro m --introduces a variable m
  induction' m with m ihypo
  -- base case
  · rw [f]
    simp?
   -- simp? returns the theorems that simp used.  You can call
   -- simp only [...] to _only_ use some theorems in the simp algorithm:
   --simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  -- ind step
  · rw [f]
    rw [ihypo]
    ring
  -- ring checks for identities in a general ring

#check f_eq_square -- We can get VSCode to display the type of our theorem.
#print f_eq_square -- Tactics build a proof term. #print lets you see the actual proof term, but this is a bit scary and you do not need this to prove things!

/-
## 5. Harder proof: Show (p-1)! = -1 mod p
Here we will walk through a harder proof

The claim is that in a domain with finitely many units, the product over all the units is -1.

Our proof we will recreate: pair up all the elements other than 1 and -1 via {x,x^{-1}}.
Each product of those two elements is 1.

In the mathlab library you can find this as theorem prod_univ_units_id_eq_neg_one
-/

/-
We will want to use the following theorems from Mathlib, plus a few others.
-/
#check Finset.prod_involution
#check Units.inv_eq_self_iff
#check FiniteField.prod_univ_units_id_eq_neg_one

theorem LecFeb9 {K} [CommRing K] [IsDomain K] [Fintype Kˣ] [DecidableEq Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by
  --first we remove 1 and -1 from our list
  let K_times_without_minus_1 : Finset Kˣ := Finset.univ.erase (-1)
  have h : (∏ x ∈ K_times_without_minus_1, x) = 1 := by
    -- Fill in proof here
    sorry
  -- Use h to complete proof here
  sorry


/-
### George's Expanded Proof for clarity / illustration purposes.
theorem LecFeb9 {K} [CommRing K] [IsDomain K] [Fintype Kˣ] [DecidableEq Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by

  --first we remove 1 and -1 from our list
  let K_times_without_minus_1 : Finset Kˣ := Finset.univ.erase (-1)
  have h : (∏ x ∈ K_times_without_minus_1, x) = 1 := by
    refine Finset.prod_involution (s := K_times_without_minus_1) (f := fun x => x) (fun x _ => x⁻¹) ?_ ?_ ?_ ?_
    · simp
    · intro a ha hax
      simp [Units.inv_eq_self_iff]
      simp at hax
      refine ⟨hax, ?_⟩
      unfold K_times_without_minus_1 at ha
      apply Finset.ne_of_mem_erase at ha
      exact ha
    · intro a ha
      simp [K_times_without_minus_1]
      unfold K_times_without_minus_1 at ha
      apply Finset.ne_of_mem_erase at ha
      rw [inv_eq_iff_eq_inv]
      exact ha
    · intro a ha
      simp
  simp[K_times_without_minus_1] at h
  rw[<- Finset.prod_erase_eq_div (by simp)] at h
  rw[<- mul_left_cancel_iff (a := -1) ] at h
  rw[Finset.mul_prod_erase (a := -1) (s := Finset.univ) (f := fun x => x) (by simp)] at h
  simp [h]
-/

/-
### Mathlib's Short proof
theorem prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by
  classical
    have : (∏ x ∈ (@univ Kˣ _).erase (-1), x) = 1 :=
      prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a => by simp +contextual [Units.inv_eq_self_iff])
        (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
    rw [← insert_erase (mem_univ (-1 : Kˣ)), prod_insert (notMem_erase _ _), this, mul_one]
-/

namespace lean_lectures

def feb9Message : String :=
  "Lean lecture Feb 9"

def feb9Nat : Nat :=
  9

end lean_lectures
