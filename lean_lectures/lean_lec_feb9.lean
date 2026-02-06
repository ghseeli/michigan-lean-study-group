import Mathlib.Tactic
/-!
# lean_lec_feb9

Scratchpad / lecture file for Feb 9.

-/



/-Logistics
## 1. Discuss goals for the study group


## 2. Next few mini-lectures
ideally we have some formal proof, type theory, theory heavy lectures
* speaker for type theory?
* speaker for BLAH-BLAH correspondence

-/

/-
## 3. Natural Numbers Game Takeaways
fun exercises, but somewhat painful to do. Mimics working with lean but feeds you the important tactics/theorems instead of you looking them up

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



/-The rewrite tactic `rw` replaces occurrences of the left-hand side of an equation with the right-hand side.

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
-/

def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => 2 * n + 1 + f n

#check f

#eval f 0
#eval f 1
#eval f 2
#eval f 3

theorem f_eq_square : ∀ n, f n = n^2 := by
  intro m --introduces a variable m
  induction' m with m ihypo
  -- base case
  ·rw [f]
   simp?
   -- simp? returns the theorems that simp used.  You can call
   -- simp only [...] to _only_ use some theorems in the simp algorithm:
   --simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  -- ind step
  rw [f]
  rw [ihypo]
  ring
  -- ring checks for identities in a general ring
#check f_eq_square --not sure what this does



namespace lean_lectures

def feb9Message : String :=
  "Lean lecture Feb 9"

def feb9Nat : Nat :=
  9

end lean_lectures
