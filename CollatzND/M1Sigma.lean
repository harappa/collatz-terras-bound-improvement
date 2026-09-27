import CollatzProof.M1.Sigma
import CollatzND.Rhin

/-!
# Removing the Rhin-type hypothesis from the stopping-time version of the main theorem (Theorem 1.2 and Corollary 1.3 of the paper)

`sigma_main` and `divergent_count` in `lean/CollatzProof/M1/Sigma.lean` take `RhinHyp` as a hypothesis.
We prove `RhinHyp` from `existsPhaseGapRhin` of Mazur's formalization (`CollatzND.rhin_logb`), so that the only remaining hypothesis is Theorem 2 of Bugeaud (2002) (`BugeaudHyp`).
-/

namespace CollatzND

/-- `RhinHyp` (`‖q log₂ 3‖ ≥ C q^{−κ}`) follows from Mazur's formalization. -/
theorem rhinHyp_holds : Collatz.M1.RhinHyp := by
  obtain ⟨C, κ, hC, h⟩ := rhin_logb
  exact ⟨C, κ, hC, fun q hq => by simpa [Collatz.M1.lam] using h q hq⟩

/-- Theorem 14.4 (stopping-time version, qualitative form): assumes only Theorem 2 of Bugeaud (2002). -/
theorem m1_sigma (hBug : Collatz.M1.BugeaudHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
    ∃ ε > 0, ∃ K0 : ℕ, ∀ K ≥ K0,
      (Collatz.M1.SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - Collatz.M1.cc) - ε) * K) :=
  Collatz.M1.sigma_main hBug rhinHyp_holds α hα hα'

/-- Corollary 14.5 (integers with infinite stopping time, qualitative form): assumes only Theorem 2 of Bugeaud (2002). -/
theorem m1_divergent (hBug : Collatz.M1.BugeaudHyp) :
    ∃ ε > 0, ∃ x0 : ℕ, ∀ x ≥ x0, (Collatz.M1.DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - Collatz.M1.cc - ε) :=
  Collatz.M1.divergent_count hBug rhinHyp_holds

end CollatzND
