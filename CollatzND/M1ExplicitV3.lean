import CollatzProof.M1.ExplicitV3
import CollatzND.M1Sigma

/-!
# The main theorems of version 3 of the proof manuscript (revision r7 of the paper): removing the Rhin-type hypothesis from the stopping-time version

`sigma_v3`, `sigma_v3_06` and `divergent_count_v3` in `CollatzProof/M1/ExplicitV3.lean` take `RhinHyp` as a hypothesis.
As in `M1Explicit.lean` (version 2), we prove `RhinHyp` from `existsPhaseGapRhin` of Mazur's formalization (`rhinHyp_holds`),
so that the only remaining hypothesis is the transcription of Theorem 1 of Bugeaud (2002) (`Thm1G1 8`).
-/

namespace CollatzND

/-- Theorem 14.4 (Theorem 17.3 of the paper; stopping-time version, v3, `α = 0.6`): `F_σ(0.6) ≤ 0.6(1 − c) − 2.46×10^{−11}`.
Assumes only Theorem 1 of Bugeaud (2002). -/
theorem m1_sigma_v3_06 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (Collatz.M1.SigmaCount K ⌊(2:ℝ) ^ ((0.6:ℝ) * K)⌋₊ : ℝ) ≤
        (2:ℝ) ^ ((0.6 * (1 - Collatz.M1.cc) - 2.46e-11) * K) :=
  Collatz.M1.sigma_v3_06 hB1 rhinHyp_holds

/-- Theorem 14.4 (Theorem 17.3 of the paper; stopping-time version, v3, range version): for `α ∈ [0.5114, 0.659]` and `ε < 2.18δ²(1 − α)` (`δ = 5.3116×10^{−6}`),
`F_σ(α) ≤ α(1 − c) − ε`. Assumes only Theorem 1 of Bugeaud (2002). -/
theorem m1_sigma_v3 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) (α : ℝ) (hα : 0.5114 ≤ α) (hα' : α ≤ 0.659)
    (ε : ℝ) (hε : ε < 2.18 * Collatz.M1.deltaV3 ^ 2 * (1 - α)) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (Collatz.M1.SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - Collatz.M1.cc) - ε) * K) :=
  Collatz.M1.sigma_v3 hB1 rhinHyp_holds α hα hα' ε hε

/-- Corollary 14.5 (Corollary 17.4 of the paper; integers with infinite stopping time, v3): `#{n ≤ x | σ(n) = ∞} ≤ x^{1 − c − 5.84×10^{−11}}`.
Assumes only Theorem 1 of Bugeaud (2002). -/
theorem m1_divergent_v3 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) :
    ∃ x0 : ℕ, ∀ x ≥ x0, (Collatz.M1.DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - Collatz.M1.cc - 5.84e-11) :=
  Collatz.M1.divergent_count_v3 hB1 rhinHyp_holds

/-- Theorem 14.4 (Theorem 1.2 of the paper; stopping-time version, qualitative form, all `α ∈ (1/2, 0.659]`): assumes only Theorem 1 of Bugeaud (2002). -/
theorem m1_sigma_thm1 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
    ∃ ε > 0, ∃ K0 : ℕ, ∀ K ≥ K0,
      (Collatz.M1.SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - Collatz.M1.cc) - ε) * K) :=
  Collatz.M1.sigma_main_thm1 hB1 rhinHyp_holds α hα hα'

/-- Corollary 14.5 (Corollary 1.3 of the paper; qualitative form): assumes only Theorem 1 of Bugeaud (2002). -/
theorem m1_divergent_thm1 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) :
    ∃ ε > 0, ∃ x0 : ℕ, ∀ x ≥ x0, (Collatz.M1.DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - Collatz.M1.cc - ε) :=
  Collatz.M1.divergent_count_thm1 hB1 rhinHyp_holds

end CollatzND
