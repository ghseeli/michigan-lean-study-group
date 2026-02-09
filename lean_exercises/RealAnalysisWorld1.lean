/--
# Real Analysis Game — World 1 (Lecture 1) cheat-sheet file

This file is meant to mirror the **first world** of Alex Kontorovich's
*Real Analysis, The Game*, i.e. the introductory world on basic Lean tactics.

The official game world focuses on the tactics:

* `exact`
* `rfl`
* `rewrite` (in standard Lean this is usually written `rw`)
* `ring_nf`
* `use`
* `intro`
* `specialize`
* `choose`

Below are small theorems ("levels") whose proofs use *only* these tactics
(and very basic core syntax).  Each proof is written step-by-step and every
line is preceded by a short hint about what to do.

# You will probably need to use the tactic reference for these exercises: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/ or google how to use some of the tactics


If you want this file to line up *exactly* with the in-game statements,
replace each `theorem LevelX_...` statement with the statement from the game;
the proof scripts (and the style of hints) should transfer almost verbatim.
-/

import Mathlib

namespace RealAnalysisGame.World1

/-!
## Level 1: `apply`
-/

example (x : ℝ) (h : x = 5) : x = 5 := by
  sorry

/-!

## Level 3: `rewrite` / `rw`

In Lean 4, the tactic is usually `rw`.
In the game, the tactic may be presented as `rewrite`.
-/

example (x y : ℝ) (Bob : x = 2) : x + y = 2 + y := by
  sorry

/-!
## Level 4: `ring_nf`

`ring_nf` normalizes ring expressions.
-/

example (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  sorry

/-!
## Level 5: `use`

`use t` provides a witness for an existential goal `∃ x, ...`.
-/

example (x y : ℝ) : ∃ (c : ℝ), (x + y)^4 = x^4 + 4*x^3*y + c*x^2*y^2 + 4*x*y^3 + y^4 := by
  sorry

/-!
## Level 6: `intro`

`intro h` turns a goal `P → Q` into a goal `Q` under a new hypothesis `h : P`.
-/

example : ∀ ε : ℝ, ε > 0 → (ε + 1)^2 = (ε + 1)^2 := by
  sorry

/-!
## Level 7: `specialize`

`specialize h t` applies a universally quantified hypothesis `h : ∀ x, ...`
 to a specific term `t`.
-/

example (t : ℝ) (t_pos : t > 0) (f : ℝ → ℝ) (hf : ∀ x > 0, f (x) = x^2) : f (t) = t^2 := by
  sorry
/-
## Level 8: `choose`

`choose` extracts witnesses from hypotheses of the form `∀ x, ∃ y, ...`.

In core Lean/mathlib, the idiom is:

```
  choose g hg using h
```

which produces a function `g` and proof `hg : ∀ x, ... (g x) ...`.

In the game, there is also a `choose` *tactic* that performs a similar action.
-/

example (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  sorry

--use a bunch of tactics to prove the following clear statement
example (f : ℝ → ℝ) (h_existential : ∃ (a : ℝ), f (a) = 3) (h_universal : ∀ x > 0, f (x + 1) = f (x) + 9) : ∃ (b : ℝ), ∀ y > 0, f (y + 1)^2 = (f (y) + (f b)^2)^2 := by
  sorry
end RealAnalysisGame.World1
