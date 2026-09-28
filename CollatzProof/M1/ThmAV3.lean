import CollatzProof.M1.S4

/-!
# Version 3 of the proof manuscript: Theorem A (v3) and Corollary A (v3) (Section 6 of the paper, revision r7)

§4.2 of version 3 of the proof manuscript (Section 6 of the paper). `R_δ` of Definition 1.10 (v3) is `RdeltaG 1.38 4.48 δ`
(`0 ≤ h_L ≤ 4.48δ²q`, `0 < h_p ≤ 1.38δq`; Definition 3.12 of the paper), (WF)(δ) is `WFG 1.38 4.48 δ`, and `δ ≤ 10^{−4}`.
The assembly uses the same general forms as version 2 (`C_thmAG`, `C_corAG` in `S4.lean`); only the constants change.

**Differences from the proof in the manuscript (§4.2.2)** (same conclusion, constants at least as good as in the manuscript; for the same reasons as in the remark in `S4.lean` for version 2):
- `S₁`: instead of step 1 of the manuscript (a lower bound for `|𝒫_P|`, slope `1.4412`), the Chernoff-type upper bound is used directly, and the gain is
  `1 − 1.38((1−c) + t*)/2 ≥ 0.0077` (`(1−c) + t* < 1.4381`). Here we use `0.0055`, as in the manuscript.
- `S₂`: as in the manuscript, `4.48t* ≥ 4.48·0.488 = 2.18624 ≥ 2.18`.
- `S₃`: instead of Pinsker's inequality (coefficient `2.18596` in the manuscript), a tilted Chernoff form with slope `z = 1 + 15δ/4` (`C_S3_gainG`).
  The main term of the coefficient is `ρ_c(1.38)²/(2(1−ρ_c) ln 2) ≈ 2.35`; what is shown here is `−1.52δ²` (natural logarithm) in `C_polyQ_v3`, whence
  `1.52/ln 2 ≥ 2.19 ≥ 2.18`.
- The coefficient `2.18` of Corollary A (v3) is the smaller of the coefficients of `S₂` and `S₃`; since `2.18δ ≤ 0.0055` (`δ ≤ 10^{−4}`), it also absorbs the term of `S₁`.
-/

namespace Collatz.M1

open Finset

/-- The polynomial estimate (v3, `κ = 15/4`, `a = 1.38`): `δ²A + δ³B + δ⁴C ≤ −1.52δ²` (`0 < δ ≤ 10^{−4}`, `ρ = ρ_c`).
`A = ρ(κ²(1−ρ)/2 − aκ) ≤ −1.627` (decreasing in `ρ ∈ (0.6309, 0.631)`, `−1.62757` at `ρ = 0.6309`), `B ≤ 100`, `C ≤ 92`. -/
lemma C_polyQ_v3 (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-4) :
    δ ^ 2 * (rhoc * ((15 / 4 : ℝ) ^ 2 / 2 * (1 - rhoc) - 1.38 * (15 / 4))) +
      δ ^ 3 * (rhoc * (2 * (15 / 4 : ℝ) ^ 3 * (rhoc ^ 2 + 1) + 1.38 * (15 / 4) ^ 2 / 2)) +
        δ ^ 4 * (rhoc * (2 * 1.38 * (15 / 4 : ℝ) ^ 3)) ≤ -1.52 * δ ^ 2 := by
  obtain ⟨h1, h2⟩ := rhoc_bounds
  set ρ := rhoc with hρ
  have hρ0 : 0 < ρ := by linarith
  have hA : ρ * ((15 / 4 : ℝ) ^ 2 / 2 * (1 - ρ) - 1.38 * (15 / 4)) ≤ -1.627 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1.le) (show (0:ℝ) ≤ 7.03125 * (ρ + 0.6309) - 1.85625 by linarith)]
  have hB : ρ * (2 * (15 / 4 : ℝ) ^ 3 * (ρ ^ 2 + 1) + 1.38 * (15 / 4) ^ 2 / 2) ≤ 100 := by
    have h3 : ρ ^ 2 ≤ 0.631 ^ 2 := by nlinarith
    have h4 : ρ * (2 * (15 / 4 : ℝ) ^ 3 * (ρ ^ 2 + 1) + 1.38 * (15 / 4) ^ 2 / 2) ≤
        0.631 * (2 * (15 / 4 : ℝ) ^ 3 * (0.631 ^ 2 + 1) + 1.38 * (15 / 4) ^ 2 / 2) := by
      apply mul_le_mul h2.le _ (by positivity) (by norm_num)
      linarith
    have h5 : (0.631 : ℝ) * (2 * (15 / 4 : ℝ) ^ 3 * (0.631 ^ 2 + 1) + 1.38 * (15 / 4) ^ 2 / 2) ≤ 100 := by
      norm_num
    linarith
  have hC : ρ * (2 * 1.38 * (15 / 4 : ℝ) ^ 3) ≤ 92 := by nlinarith
  have hB0 : 0 ≤ ρ * (2 * (15 / 4 : ℝ) ^ 3 * (ρ ^ 2 + 1) + 1.38 * (15 / 4) ^ 2 / 2) := by positivity
  have hC0 : 0 ≤ ρ * (2 * 1.38 * (15 / 4 : ℝ) ^ 3) := by positivity
  have hd2 : 0 < δ ^ 2 := by positivity
  have hd3 : δ ^ 3 ≤ 1e-4 * δ ^ 2 := by
    have : δ ^ 3 = δ * δ ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hδ1 hd2.le
  have hd4 : δ ^ 4 ≤ 1e-8 * δ ^ 2 := by
    have : δ ^ 4 = (δ * δ) * δ ^ 2 := by ring
    rw [this]; apply mul_le_mul_of_nonneg_right _ hd2.le; nlinarith
  have t1 : δ ^ 2 * (ρ * ((15 / 4 : ℝ) ^ 2 / 2 * (1 - ρ) - 1.38 * (15 / 4))) ≤ δ ^ 2 * (-1.627) :=
    mul_le_mul_of_nonneg_left hA hd2.le
  have t2 : δ ^ 3 * (ρ * (2 * (15 / 4 : ℝ) ^ 3 * (ρ ^ 2 + 1) + 1.38 * (15 / 4) ^ 2 / 2)) ≤
      (1e-4 * δ ^ 2) * 100 := mul_le_mul hd3 hB hB0 (by positivity)
  have t3 : δ ^ 4 * (ρ * (2 * 1.38 * (15 / 4 : ℝ) ^ 3)) ≤ (1e-8 * δ ^ 2) * 92 :=
    mul_le_mul hd4 hC hC0 (by positivity)
  linarith

set_option maxHeartbeats 1000000 in
/-- The gain of `S₃` (v3): if `h_p ≥ 1.38δq`, `P ≤ q` and `0 < δ ≤ 10^{−4}`, then
`(1 + ρ_c ε)^P / (1+ε)^{L_p} ≤ 2^{−2.18δ²q}` (`ε = 15δ/4`). -/
lemma C_S3_gain_v3 (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-4) (P Lq q : ℕ) (hPq : (P : ℝ) ≤ q)
    (hhp : 1.38 * δ * q ≤ lam * Lq - P) :
    (1 + rhoc * ((1 + 15 / 4 * δ) - 1)) ^ P / (1 + 15 / 4 * δ) ^ Lq ≤
      (2:ℝ) ^ (-(2.18 * δ ^ 2 * q)) :=
  C_S3_gainG 1.38 (15 / 4) 1.52 2.18 δ hδ (by norm_num) (by linarith) (by norm_num) (by norm_num)
    (C_polyQ_v3 δ hδ hδ1) P Lq q hPq hhp

/-- Concrete form of Theorem A (v3) (`C₀ = 32`, `N₀ = 3`, `q₀ = 2`): if `(WF)(δ)` (with `R_δ` of v3) holds at `(s, q)`, then
`#(𝒩_K ∩ [1, 2^s)) ≤ 32(s+2)³ 2^{(1−c)s}(2^{−(1−c)(s−q)/2} + 2^{−0.0055δq} + 2^{−2.18δ²q})`. -/
theorem C_thmA_v3 (s q : ℕ) (δ : ℝ) (hq : 2 ≤ q) (hs1 : 1 < (s : ℝ) / q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1e-4) (hWF : WFG 1.38 4.48 δ s q) :
    (NKcount (s + q) (2 ^ s - 1) : ℝ) ≤ 32 * ((s : ℝ) + 2) ^ 3 * (2:ℝ) ^ ((1 - cc) * s) *
      ((2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(0.0055 * δ * q)) +
        (2:ℝ) ^ (-(2.18 * δ ^ 2 * q))) :=
  C_thmAG s q 1.38 4.48 δ (15 / 4) 0.0055 2.18 hq hs1 hδ (by linarith) (by positivity) (by norm_num)
    (by norm_num) (fun P Lq q hPq hhp => C_S3_gain_v3 δ hδ hδ1 P Lq q hPq hhp) hWF

/-- **Theorem A (v3)** (§4.2.2 of version 3 of the manuscript; Theorem A of the paper): if (WF)(δ) (with `R_δ` of Definition 1.10 of v3: `h_L ≤ 4.48δ²q`, `h_p ≤ 1.38δq`) holds
at `(s, q)`, then `#(𝒩_K ∩ [1, 2^s))` is at most `2^{(1−c)s + O(log s)}(2^{−(1−c)(s−q)/2} + 2^{−0.0055δq} + 2^{−2.18δ²q})`
(the factor `2^{O(log s)}` is `C₀(s+2)^{N₀}`; `0 < δ ≤ 10^{−4}`). -/
theorem thmA_v3 : ∃ C0 : ℝ, ∃ N0 q0 : ℕ, ∀ (s q : ℕ) (δ : ℝ), q0 ≤ q → 1 < (s : ℝ) / q →
    (s : ℝ) / q ≤ 1.94 → 0 < δ → δ ≤ 1e-4 → WFG 1.38 4.48 δ s q →
    (NKcount (s + q) (2 ^ s - 1) : ℝ) ≤ C0 * ((s : ℝ) + 2) ^ N0 * (2:ℝ) ^ ((1 - cc) * s) *
      ((2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(0.0055 * δ * q)) +
        (2:ℝ) ^ (-(2.18 * δ ^ 2 * q))) :=
  ⟨32, 3, 2, fun s q δ hq hs1 _ hδ hδ1 hWF => C_thmA_v3 s q δ hq hs1 hδ hδ1 hWF⟩

/-- **Corollary A (v3)** (§4.2.2 of version 3 of the manuscript; Corollary A of the paper): let `1/2 < α ≤ 0.659` and `0 < δ ≤ 10^{−4}`. If (WF)(δ) (with `R_δ` of v3) holds for all
sufficiently large `K`, then for every `ε < min(2.18δ²(1−α), (1−c)(2α−1)/2)` and all sufficiently large `K`,
`#(𝒩_K ∩ [1, 2^{αK}]) ≤ 2^{(α(1−c) − ε)K}`. -/
theorem corA_v3 (α δ : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) (hδ : 0 < δ) (hδ' : δ ≤ 1e-4)
    (hWF : ∃ K1 : ℕ, ∀ K ≥ K1, WFG 1.38 4.48 δ (sOf α K) (K - sOf α K)) (ε : ℝ)
    (hε : ε < min (2.18 * δ ^ 2 * (1 - α)) ((1 - cc) * (2 * α - 1) / 2)) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) :=
  C_corAG α 1.38 4.48 δ (15 / 4) 0.0055 2.18 2.18 hα hα' hδ (by linarith) (by positivity) (by norm_num)
    (by norm_num) (fun P Lq q hPq hhp => C_S3_gain_v3 δ hδ hδ' P Lq q hPq hhp) (by norm_num) le_rfl
    (by linarith) (by nlinarith) hWF ε hε

end Collatz.M1
