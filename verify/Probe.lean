import CollatzND.M1ExplicitV3
import CollatzND.M1Explicit
import CollatzProof.M1.BugeaudBridge

/-!
# Statements, definitions and axioms of the formalization

Run from the bundle root after `lake build`:

    lake env lean verify/Probe.lean

This file is not part of any library; it only displays the main theorems, the definitions that occur in their
statements, and the axioms each main theorem depends on. Every `#print axioms` below should report exactly
`[propext, Classical.choice, Quot.sound]`. Bugeaud's theorems are not axioms: Theorem 1 (case `g = 1`, `m = 8`) is the
explicit hypothesis `Collatz.M1.Bugeaud.Thm1G1 8` of the main theorems of revision r7, and Theorem 2 enters the
statements of revision r6 as the explicit hypothesis `Collatz.M1.BugeaudHyp`.
-/

/-! ## Main theorems under Theorem 1 of Bugeaud (2002) (revision r7) -/

-- Theorem 1.1 of the paper, qualitative form: some `ε > 0` for every `α ∈ (1/2, 0.659]`.
#check Collatz.M1.m1_main_thm1
-- Theorem 1.1 with explicit values: `ε < 2.18 δ² (1 − α)` with `δ = deltaV3 = 5.3116e-6`, `α ∈ [0.5114, 0.659]`;
-- in particular `ε(0.6) = 2.46e-11`.
#check Collatz.M1.m1_v3
#check Collatz.M1.m1_v3_06
-- Theorem 1.2 (stopping time), qualitative and explicit; `RhinHyp` is discharged by Mazur's formalization.
#check CollatzND.m1_sigma_thm1
#check CollatzND.m1_sigma_v3
#check CollatzND.m1_sigma_v3_06
-- Corollary 1.3 (integers with infinite stopping time), qualitative and with the exponent `1 − c − 5.84e-11`.
#check CollatzND.m1_divergent_thm1
#check CollatzND.m1_divergent_v3

/-! ## Main theorems under Theorem 2 of Bugeaud (2002) (revision r6) -/

-- The qualitative theorems of revision r6.
#check Collatz.M1.m1_main
#check CollatzND.m1_sigma
#check CollatzND.m1_divergent
-- The explicit values of revision r6 (`ε(0.6) = 5.35e-14`, exponent `1 − c − 1.33e-13`), formalized since then.
#check Collatz.M1.m1_explicit_06
#check CollatzND.m1_sigma_explicit_06
#check CollatzND.m1_divergent_explicit

/-! ## Results about the hypotheses -/

-- Proposition 15.5 of the paper (the height condition from Theorem 1 of Bugeaud, window width `c_D ≤ 9e-3`).
#check Collatz.M1.hgt_thm1
-- The premises of `Thm1G1 8` can be satisfied simultaneously, so `Thm1G1 8` is not vacuously true.
#check Collatz.M1.thm1G1_eight_premises_satisfiable
-- `Thm1G1` is equivalent to the form stated with the heights of the fractions in lowest terms.
#check Collatz.M1.Bugeaud.thm1G1_iff_red
-- The bridge from a transcription of Theorem 2 of Bugeaud (general `m`, `μ`) to `BugeaudHyp`.
#check Collatz.M1.Bugeaud.bugeaudHyp_of_thm2
-- The Rhin-type bound `RhinHyp`, proved from Mazur's formalization.
#check CollatzND.rhinHyp_holds

/-! ## Axioms -/

#print axioms Collatz.M1.m1_main_thm1
#print axioms Collatz.M1.m1_v3
#print axioms Collatz.M1.m1_v3_06
#print axioms CollatzND.m1_sigma_thm1
#print axioms CollatzND.m1_sigma_v3
#print axioms CollatzND.m1_sigma_v3_06
#print axioms CollatzND.m1_divergent_thm1
#print axioms CollatzND.m1_divergent_v3
#print axioms Collatz.M1.m1_main
#print axioms CollatzND.m1_sigma
#print axioms CollatzND.m1_divergent
#print axioms Collatz.M1.m1_explicit_06
#print axioms CollatzND.m1_sigma_explicit_06
#print axioms CollatzND.m1_divergent_explicit
#print axioms Collatz.M1.hgt_thm1
#print axioms Collatz.M1.thm1G1_eight_premises_satisfiable
#print axioms Collatz.M1.Bugeaud.thm1G1_iff_red
#print axioms Collatz.M1.Bugeaud.bugeaudHyp_of_thm2
#print axioms CollatzND.rhinHyp_holds

/-! ## The hypothesis `Thm1G1` (Theorem 1 of Bugeaud (2002), `g = 1`) and its parts -/

#print Collatz.M1.Bugeaud.Thm1G1
#print Collatz.M1.Bugeaud.Prem
#print Collatz.M1.Bugeaud.cond1
#print Collatz.M1.Bugeaud.logHt
#print Collatz.M1.Bugeaud.bB
#print Collatz.M1.Bugeaud.factProd
#print Collatz.M1.Bugeaud.gam1
#print Collatz.M1.Bugeaud.gam2
#print Collatz.M1.Bugeaud.hExp
#print Collatz.M1.Bugeaud.hMax
#print Collatz.M1.Bugeaud.set1
#print Collatz.M1.Bugeaud.set2
#print Collatz.M1.Bugeaud.H1
#print Collatz.M1.Bugeaud.H2
#print Collatz.M1.Bugeaud.VpGe
#print Collatz.M1.Bugeaud.vm
#print Collatz.M1.Bugeaud.vmNat

/-! ## The hypotheses `BugeaudHyp` (Theorem 2 of Bugeaud (2002)) and `RhinHyp` -/

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
-- The value of `δ` in the explicit theorems of revision r7 (and `deltaE`, that of revision r6).
#print Collatz.M1.deltaV3
#print Collatz.M1.deltaE

/-! ## Sanity checks of the definitions -/

example : Collatz.T 7 = 11 := by decide
example : Collatz.T 10 = 5 := by decide
example : Collatz.T 1 = 2 := by decide
