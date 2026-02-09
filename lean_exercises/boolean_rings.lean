/-This exercises is from https://people.math.harvard.edu/~pmwood/Teaching/2023sMath161/
-/

/-
The notion of a ring is discussed in the textbook:
https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#proving-identities-in-algebraic-structures

A *Boolean* ring satisfies the additional property that for every `x`, `x^2 = x`.
You can read about Boolean rings here:
https://en.wikipedia.org/wiki/Boolean_ring
-/

variable {R : Type*} [Ring R]

-- This is the assumption that makes `R` a Boolean ring:
variable (idem : ∀ x : R, x ^ 2 = x)

-- This adds `idem` as a hypothesis to every theorem:
include idem

/-
This exercise asks you to prove that every Boolean ring is commutative, i.e.
satisfies `x * y = y * x` for every `x` and `y`. Unfortunately, we cannot use the
`ring` tactic along the way, since it only works once we know a ring is commutative.
So you will have to rely on theorems like `mul_add`, `add_mul`, etc. in the textbook.
-/

-- This is useful:
theorem mul_idem (x : R) : x * x = x :=
by rw [←pow_two, idem]

-- Unfortunately, you have to write `mul_idem idem` to use it.
example (x y : R) : (x + y) * (x + y) = x + y :=
by rw [mul_idem idem]

/-
Prove the following theorem, following the calculation in Wikipedia:
x + x = (x+x)^2 = x^2 + x^2 + x^2 + x^2 = (x + x) + (x + x).
-/

theorem add_self (x : R) : x + x = 0 := by
  have h1 : x + x = (x + x) + (x + x) :=
  calc
    x + x = (x + x)^2 := by
      sorry
    _ = x + x + (x + x) := by
      sorry
  have h2 : (x + x) + (x + x) - (x + x) = (x + x) - (x + x) := by
     rw [←h1]
  rw [add_sub_cancel_right, sub_self] at h2
  exact h2

-- Note: again, to use this theorem you have to mention `idem` explicitly
example (y : R) : y + y = 0 :=
add_self idem y

/-
Prove `neg_eq_self` using the calculation `-x = 0 - x = x + x - x = x`. You can use the theorems
`zero_sub` and `add_sub_cancel`, as well as `add_self idem`.
-/

theorem neg_eq_self (x : R) : -x = x := by
  sorry

/-
This is a corollary.
-/

theorem sub_eq_add (x y : R) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_self idem]

/-
Prove this, using the calculation `x = x + y - y = 0 - y = -y = y`.
-/
theorem eq_of_add_eq_zero {x y : R} (h : x + y = 0) :
  x = y := by
  sorry

/- Finally, prove `mul_comm` using the following argument from Wikipedia:

`0 + x + y = x + y = (x + y)^2 = x^2 + xy + yx + y^2 = xy + yx + x + y`

You can use the `abel` tactic to rearrange sums.
-/

example (x y : R) : x + x * y + y * x + y = x * y + y * x + x + y :=
by abel

theorem mul_comm (x y : R) : x * y = y * x := by
  have h1 : 0 + (x + y) = (x * y + y * x) + (x + y) :=
  calc
    0 + (x + y) = (x + y)^2 := by
      sorry
    _ = x * y + y * x + (x + y) := by
      sorry
  have h2 : 0 = x * y + y * x := by
    exact add_right_cancel h1
  show x * y = y * x
  -- post to Ed Discussion if you can figure out why Lean wants `change` here instead of `show`
  -- (or you post if you observe a different behavior here)
  exact eq_of_add_eq_zero idem h2.symm

end boolean_ring_exercise
