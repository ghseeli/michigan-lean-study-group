/-This collage of exercises was put together in https://people.math.harvard.edu/~pmwood/Teaching/2023sMath161/
using exercises from the Mathematics in Lean online textbook

-/

import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

--set_option warningAsError false
/-
FIRST EXERCISE: Strict monotonicity

Section 3.1 of MIL discusses the `monotone` predicate. There is also a strict
version. Prove the theorems below, *and* come up with suitable names
(in other words, replace `example` with `theorem foo`.)

(Don't use any library theorems about `strict_mono` or `monotone`! You should
only use basic properties of orderings.)
-/

#print Monotone
#print StrictMono

namespace strict_mono_exercise

variable (f : ℝ → ℝ) (g : ℝ → ℝ)

example (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f + g) := by
  sorry


-- You'll have to guess at the name of a theorem for this one.
example (c : ℝ) (hf : StrictMono f) (hc : 0 < c) :
  StrictMono (fun x ↦ c * f x) := by
  sorry

-- This is trickier than you might think. Use `by_cases h : a = b` to split
-- on cases whether `a = b`. You can also use `lt_of_le_of_ne`.

example (hf : StrictMono f) : Monotone f := by
  sorry


/-
The following (trivial) example shows how to use trichotomy. You do not need
to fully understand the pattern now; you can take it as a black box.
-/

example (x1 x2 : ℝ) : x1 ≤ x2 ∨ x2 < x1 := by
  rcases lt_trichotomy x1 x2 with h | h | h
  { -- In this case, we have `h : x1 < x2`.
    left
    apply le_of_lt h }
  { -- In this case, we have `h : x1 = x2`.
    left
    rw [h] }
  -- In this case, we have `h : x2 < x1`
  right
  exact h

-- another example

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt


open Function

/-
Here is an example that shows that `x ↦ x + 1` is injective.
-/

example : Injective (fun x ↦ x + 1) := by
  intros x1 x2 h
  dsimp at h -- this makes `h` more readable
  exact add_right_cancel h


/-
Show that every strictly monotone function is injective.
-/

theorem injective_of_strict_mono (hf : StrictMono f) : Injective f := by
  sorry


end strict_mono_exercise
