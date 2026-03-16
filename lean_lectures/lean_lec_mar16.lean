import Mathlib

/-!
# lean_lec_mar16

Scratchpad / lecture file for Mar 16.
-/

/-

# Live coding the Brouwer Fixed Point Theorem (a start)

A continuous map from an even dimensional sphere to itself has a fixed point.
*or*
A continuous map from a ball to itself has a fixed point if it preserves the boundary.
-/

--set_option pp.universes true
universe u

noncomputable abbrev H := AlgebraicTopology.singularHomologyFunctor (AddCommGrpCat)
noncomputable abbrev S : ℕ → TopCat  := TopCat.sphere
noncomputable abbrev D : ℕ → TopCat := TopCat.disk
abbrev S_to_S_retract (n : ℕ ) := CategoryTheory.Retract (S n) (D (n+1))

lemma H1_of_sphere
    (n : ℕ) :
    ((H n).obj (AddCommGrpCat.of ℤ)).obj (S n)
    = (AddCommGrpCat.of ℤ) := by
  sorry

#check CategoryTheory.Retract
-- f : X -> Y, Y ⊆ X, f continuous, f|_Y = id Y

lemma empty_retract (n : ℕ) :
    IsEmpty (S_to_S_retract n) := by
  sorry

def retraction {n : ℕ}
    (f : TopCat.Hom (D n) (D n))
    (hf : IsEmpty (Function.fixedPoints f.hom')) :
    S_to_S_retract n := sorry

theorem brouwer_fixed_point_theorem
    (n : ℕ)
    (f : TopCat.Hom (D.{u} n) (D.{u} n)) :
    Nonempty (Function.fixedPoints f.hom') := by
  /- 1. No retraction from disk to the sphere.
        Requires a nonzero topological invariant of the sphere (e.g., homology)
     2. H^*(disk) = 0, H¹(sphere) = ℤ -/
  by_contra!
  set ir := retraction f this
  --let ⟨i, r, ret⟩ := retraction f this
  have hempty := empty_retract.{u} n
  exact hempty.false ir
