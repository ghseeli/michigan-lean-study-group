import Mathlib

/-!
# lean_lec_feb23

Scratchpad / lecture file for Feb 23.
-/

/-
## 1. Discuss potential formalization projects
1. General Brouwer Fixed Point Theorem (Calvin)
2. Basic facts about frieze patterns; basic claims about periodicity(Katie)
3. Geometric results about friezes (Katie)
4. Domain specific languages (formally verified in Lean) (Steven)
5. Topology of finite graphs / free groups (show subgroup of free group is a free group using graphs and covering spaces) (George)
6. Proving Stone Representation Theorem for boolean algebras (Patrick)
7. Statements involving geometric lattices; percolation theory; 2D crossing theorem (SC)
8. See https://leanprover-community.github.io/1000-missing.html for lots of ideas!


## 2. Break up and do exercises
To setup this project:
1. Go to Lean4 menu (∀ sign in VS Code) -> Open Project... -> Download Project...
2. Enter https://github.com/ghseeli/michigan-lean-study-group.git and pick where to save it
3. In your terminal (in the directory where this project was made), run `lake exe cache get` to avoid having to recompile mathlib.
4. Find the exercises in `lean_exercises` directory.

Depending on your comfort level with Lean tactics, the recommended order of exercises is
1. RealAnalysisWorld1.lean
2. monotone.lean
3. boolean_rings.lean
4. N_choose_2.lean
5. infinitely_many_primes.lean

## 3. Challenges / what has been learned?

### tactics
#### Real Analysis World
1. rfl
2. rw
3. apply
4. intro
5. specialize
#### Infinitely many primes
1. strong induction (induction n using Nat.strong_induction_on)
2. constructor

## 4. Google sheets for projects
With your umich.edu account, go to https://docs.google.com/spreadsheets/d/1boIU3XJ07rNVmrLBNgH_IfAwTjXOF5uhW01WOJK8wk4/edit?usp=sharing to propose a project!

-/
