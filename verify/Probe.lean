import CollatzND.M1Sigma

/-!
# Statements, definitions and axioms of the formalization

Run from the bundle root after `lake build`:

    lake env lean verify/Probe.lean

This file is not part of any library; it only displays the main theorems, the definitions that occur in their
statements, and the axioms each main theorem depends on. Every `#print axioms` below should report exactly
`[propext, Classical.choice, Quot.sound]`. Bugeaud (2002), Theorem 2, is not an axiom: it is the explicit
hypothesis `Collatz.M1.BugeaudHyp` of each main theorem.
-/

/-! ## Main theorems -/

-- Counting version (Theorem 1.1 of the paper): survivors of the coefficient stopping time, all `α ∈ (1/2, 0.659]`.
#check Collatz.M1.m1_main
-- Stopping-time version and divergent-orbit count, with the Rhin-type bound `RhinHyp` as a hypothesis.
#check Collatz.M1.sigma_main
#check Collatz.M1.divergent_count
-- The same two results with `RhinHyp` discharged by Mazur's formalization (only `BugeaudHyp` remains).
#check CollatzND.m1_sigma
#check CollatzND.m1_divergent
#check CollatzND.rhinHyp_holds

/-! ## Axioms -/

#print axioms Collatz.M1.m1_main
#print axioms Collatz.M1.sigma_main
#print axioms Collatz.M1.divergent_count
#print axioms CollatzND.rhinHyp_holds
#print axioms CollatzND.m1_sigma
#print axioms CollatzND.m1_divergent

/-! ## Hypotheses -/

#print Collatz.M1.BugeaudHyp
#print Collatz.M1.v8
#print Collatz.M1.v2q
#print Collatz.M1.MulIndep
#print Collatz.M1.RhinHyp

/-! ## Definitions occurring in the statements -/

-- The shortcut map `T(n) = n/2` (n even), `(3n+1)/2` (n odd).
#print Collatz.T
-- Parity word, number of ones, height, survival, and the survivor count `#(𝒩_K ∩ [1, X])`.
#print Collatz.M1.pw
#print Collatz.M1.ones
#print Collatz.M1.lam
#print Collatz.M1.hw
#print Collatz.M1.SurvW
#print Collatz.M1.NKcount
-- The constant `c = 1 − H(1/log₂ 3)`.
#print Collatz.M1.Hb
#print Collatz.M1.rhoc
#print Collatz.M1.cc
-- Stopping time: `σ(n) > K`, and the counts of `σ(n) > K` and of `σ(n) = ∞`.
#print Collatz.M1.SigmaGt
#print Collatz.M1.SigmaCount
#print Collatz.M1.DivCount

/-! ## Sanity checks of the definitions -/

example : Collatz.T 7 = 11 := by decide
example : Collatz.T 10 = 5 := by decide
example : Collatz.T 1 = 2 := by decide
