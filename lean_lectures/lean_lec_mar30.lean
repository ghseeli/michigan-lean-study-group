import Mathlib
/-!
# lean_lec_mar30

Scratchpad / lecture file for Mar 30.
-/

/-
# Suggested details for longer "drop-in" session
Date: Monday, April 6, 2026
Times:
* 10am--2pm in EH 5822
* 2pm--3pm in NUB 1507
* After 3pm in Atrium
Structure: show up and work on some project(s) together?
Projects Google Sheet: https://docs.google.com/spreadsheets/d/1boIU3XJ07rNVmrLBNgH_IfAwTjXOF5uhW01WOJK8wk4/edit?usp=sharing

# Groundwork for starting a project
* Pick a specific result/theorem, ideally not too ambitious.
* Try to make sure you understand details of proofs and have them written out somewhere (either in a reference or in your own document)
* Check the following sources for existing results
  * Mathlib reference manual: https://leanprover-community.github.io/mathlib4_docs/
  * Leansearch: https://leansearch.net/
  * Zulip chat: https://leanprover.zulipchat.com/
* Try to define the relevant structures you will work with.
  There are multiple ways to define objects in Lean
  * def (e.g., is your object just a special kind of function? E.g., matrices)
  * class (most common for a standard mathematical object/structure built on something else in a fixed way. E.g., a Group is a set with extra structure)
  * structure (most common for one-off things or structures that are not fixed once, e.g., Subgroups)
  * inductive (the base-level way to make a new object; classes and structures are just special inductives.)
  Some examples to check definitions of below:
-/
#check Matrix -- Just a function
#check LinearMap -- Structure
#check Group -- Class
#check Subgroup -- Structure
#check Nat -- Inductive

/-
# An example
Goals: define Schur polynomials in 3 ways (Weyl character formula/bi-alternant identity, Jacobi-Trudi determinant, and generating function of semistandard Young tableaux)
References: Macdonald's book on symmetric functions is a thorough reference; supplement with my own notes as necessary: https://ghseeli.github.io/grad-school-writings/class-notes/algebraic-combinatorics.pdf
Previous work:
* Some symmetric polynomials were implemented in Lean: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.html
* Fundamental theorem of symmetric polynomials: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.html
*
-/
