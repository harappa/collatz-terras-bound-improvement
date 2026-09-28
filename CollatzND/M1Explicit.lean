import CollatzProof.M1.Explicit
import CollatzND.M1Sigma

/-!
# Explicit values of revision r6 (version 2 of the proof manuscript): removing the Rhin-type hypothesis from the stopping-time version

`sigma_explicit_06` and `divergent_count_explicit` in `CollatzProof/M1/Explicit.lean` take `RhinHyp` as a hypothesis.
As in `M1Sigma.lean`, we prove `RhinHyp` from `existsPhaseGapRhin` of Mazur's formalization (`rhinHyp_holds`),
so that the only remaining hypothesis is Theorem 2 of Bugeaud (2002) (`BugeaudHyp`).
-/

namespace CollatzND

/-- Theorem 14.4 (stopping-time version, explicit value of version 2): `F_σ(0.6) ≤ 0.6(1 − c) − 5.35×10^{−14}`. Assumes only Theorem 2 of Bugeaud (2002). -/
theorem m1_sigma_explicit_06 (hBug : Collatz.M1.BugeaudHyp) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (Collatz.M1.SigmaCount K ⌊(2:ℝ) ^ ((0.6:ℝ) * K)⌋₊ : ℝ) ≤
        (2:ℝ) ^ ((0.6 * (1 - Collatz.M1.cc) - 5.35e-14) * K) :=
  Collatz.M1.sigma_explicit_06 hBug rhinHyp_holds

/-- Theorem 14.4 (stopping-time version, explicit values of version 2, range version): for `α ∈ [0.5006, 0.659]` and `ε < 1.70δ²(1 − α)` (`δ = 2.8055×10^{−7}`),
`F_σ(α) ≤ α(1 − c) − ε`. Assumes only Theorem 2 of Bugeaud (2002). -/
theorem m1_sigma_explicit (hBug : Collatz.M1.BugeaudHyp) (α : ℝ) (hα : 0.5006 ≤ α) (hα' : α ≤ 0.659)
    (ε : ℝ) (hε : ε < 1.70 * Collatz.M1.deltaE ^ 2 * (1 - α)) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (Collatz.M1.SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - Collatz.M1.cc) - ε) * K) :=
  Collatz.M1.sigma_explicit hBug rhinHyp_holds α hα hα' ε hε

/-- Corollary 14.5 (integers with infinite stopping time, explicit value of version 2): `#{n ≤ x | σ(n) = ∞} ≤ x^{1 − c − 1.33×10^{−13}}`.
Assumes only Theorem 2 of Bugeaud (2002). -/
theorem m1_divergent_explicit (hBug : Collatz.M1.BugeaudHyp) :
    ∃ x0 : ℕ, ∀ x ≥ x0, (Collatz.M1.DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - Collatz.M1.cc - 1.33e-13) :=
  Collatz.M1.divergent_count_explicit hBug rhinHyp_holds

end CollatzND
