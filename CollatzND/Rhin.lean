import Erdos1135.ND.RhinPhaseGap

/-!
# The Rhin-type bound (the content of the hypothesis `Collatz.M1.RhinHyp` of the stopping-time version of the main theorem, Theorem 1.2 of the paper)

We rewrite `Erdos1135.ND.existsPhaseGapRhin` of Mazur's formalization (`‖q log₂ 3‖ ≥ c q^{1−14.3}`, proved in Lean)
into the same form as `Collatz.M1.RhinHyp` (`lean/CollatzProof/M1/Sigma.lean`). `lam = Real.logb 2 3` is written with its definition unfolded.
Once the formalization of the main theorem is closed, `RhinHyp` is discharged by this theorem (`CollatzND/M1Sigma.lean`).
-/

namespace CollatzND

open Erdos1135.ND

/-- `‖q log₂ 3‖ ≥ C q^{−13.3}` (`q ≥ 1`). The form of `RhinHyp` with `lam` unfolded to `Real.logb 2 3`. -/
theorem rhin_logb :
    ∃ C κ : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q →
      C * (q : ℝ) ^ (-κ) ≤ |(q : ℝ) * Real.logb 2 3 - (round ((q : ℝ) * Real.logb 2 3) : ℝ)| := by
  obtain ⟨c, hc⟩ := existsPhaseGapRhin
  refine ⟨c, 133 / 10, hc.c_pos, fun q hq => ?_⟩
  have h := hc.gap q hq
  have hlog : logTwoThree = Real.logb 2 3 := by
    simp [logTwoThree, Real.logb]
  have hexp : (1 - (143 / 10 : ℝ)) = -(133 / 10 : ℝ) := by norm_num
  rw [hexp] at h
  simpa [nearestIntegerNorm, hlog, Real.rpow_eq_pow] using h

end CollatzND
