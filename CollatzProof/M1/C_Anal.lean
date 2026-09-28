import CollatzProof.M1.C_Count

/-!
# Auxiliary (6) for Theorem A: the analytic estimate (the gain of `S₃`)

If `h_p ≥ 1.23δq` and `P ≤ q`, then with the tilt `z = 1 + 10δ/3`,
`(1 + ρ_c(z − 1))^P / z^{L_p} ≤ 2^{−1.708δ²q}`.
Instead of step 4 in §4 of the manuscript (Pinsker's inequality, coefficient `(2/ln 2)ρ_c²(1.23 − 3.5δ)² ≥ 1.727`),
we estimate the tilted Chernoff form using the expansion of `log(1 + v)` to second order (Mathlib's `Real.abs_log_sub_add_sum_range_le`)
(the coefficient is about `ρ_c(1.23)²/(2(1−ρ_c) ln 2) − O(δ) ≥ 1.76`).
-/

namespace Collatz.M1

open Finset

/-- For `0 ≤ v ≤ 1/2`, `|log(1+v) − v + v²/2| ≤ 2v³`. -/
lemma C_log_bounds (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1 / 2) :
    v - v ^ 2 / 2 - 2 * v ^ 3 ≤ Real.log (1 + v) ∧ Real.log (1 + v) ≤ v - v ^ 2 / 2 + 2 * v ^ 3 := by
  have hx : |(-v)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg,
    abs_of_nonneg h0] at h
  have e : (0:ℝ) + (-v) ^ (0 + 1) / (↑0 + 1) + (-v) ^ (1 + 1) / (↑1 + 1) = -v + v ^ 2 / 2 := by
    push_cast; ring
  rw [add_comm 1 v] at *
  have h' : |(-v + v ^ 2 / 2) + Real.log (v + 1)| ≤ v ^ (2 + 1) / (1 - v) := by
    have : (0:ℝ) + (-v) ^ (0 + 1) / ((0:ℕ) + 1 : ℝ) + (-v) ^ (1 + 1) / ((1:ℕ) + 1 : ℝ) =
        -v + v ^ 2 / 2 := by push_cast; ring
    rw [← this]; exact h
  have hv3 : v ^ (2 + 1) / (1 - v) ≤ 2 * v ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ v ^ 3 := by positivity
    norm_num; nlinarith
  have h2 := abs_le.1 (h'.trans hv3)
  constructor <;> linarith [h2.1, h2.2]

lemma C_rhoc_lam : rhoc * lam = 1 := by
  unfold rhoc; field_simp [C_lam_pos.ne']

lemma C_polyA (ρ : ℝ) (h1 : 0.6309 < ρ) (h2 : ρ < 0.631) : ρ * (50 / 9 * (1 - ρ) - 4.1) ≤ -1.29 := by
  have hρ0 : 0 < ρ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1.le hρ0.le]

lemma C_polyB (ρ : ℝ) (h1 : 0.6309 < ρ) (h2 : ρ < 0.631) :
    ρ * (2000 / 27 * (ρ ^ 2 + 1) + 61.5 / 9) ≤ 70 := by
  have hρ0 : 0 < ρ := by linarith
  have h3 : ρ ^ 2 ≤ 0.631 ^ 2 := by nlinarith
  have h4 : ρ * (2000 / 27 * (ρ ^ 2 + 1) + 61.5 / 9) ≤
      0.631 * (2000 / 27 * (0.631 ^ 2 + 1) + 61.5 / 9) := by
    apply mul_le_mul h2.le _ (by positivity) (by norm_num)
    linarith
  have h5 : (0.631 : ℝ) * (2000 / 27 * (0.631 ^ 2 + 1) + 61.5 / 9) ≤ 70 := by norm_num
  linarith

/-- A polynomial estimate: `δ²A + δ³B + δ⁴C ≤ −1.184δ²` (`ρ ∈ (0.6309, 0.631)`, `0 < δ ≤ 10^{−3}`). -/
lemma C_polyQ (ρ δ : ℝ) (h1 : 0.6309 < ρ) (h2 : ρ < 0.631) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) :
    δ ^ 2 * (ρ * (50 / 9 * (1 - ρ) - 4.1)) +
      δ ^ 3 * (ρ * (2000 / 27 * (ρ ^ 2 + 1) + 61.5 / 9)) +
        δ ^ 4 * (ρ * (2.46 * 1000 / 27)) ≤ -1.184 * δ ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  have hA := C_polyA ρ h1 h2
  have hB := C_polyB ρ h1 h2
  have hC : ρ * (2.46 * 1000 / 27) ≤ 58 := by nlinarith
  have hB0 : 0 ≤ ρ * (2000 / 27 * (ρ ^ 2 + 1) + 61.5 / 9) := by positivity
  have hC0 : 0 ≤ ρ * (2.46 * 1000 / 27) := by positivity
  have hd2 : 0 < δ ^ 2 := by positivity
  have hd3 : δ ^ 3 ≤ 1e-3 * δ ^ 2 := by
    have : δ ^ 3 = δ * δ ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hδ1 hd2.le
  have hd4 : δ ^ 4 ≤ 1e-6 * δ ^ 2 := by
    have : δ ^ 4 = (δ * δ) * δ ^ 2 := by ring
    rw [this]; apply mul_le_mul_of_nonneg_right _ hd2.le; nlinarith
  have t1 : δ ^ 2 * (ρ * (50 / 9 * (1 - ρ) - 4.1)) ≤ δ ^ 2 * (-1.29) :=
    mul_le_mul_of_nonneg_left hA hd2.le
  have t2 : δ ^ 3 * (ρ * (2000 / 27 * (ρ ^ 2 + 1) + 61.5 / 9)) ≤ (1e-3 * δ ^ 2) * 70 :=
    mul_le_mul hd3 hB hB0 (by positivity)
  have t3 : δ ^ 4 * (ρ * (2.46 * 1000 / 27)) ≤ (1e-6 * δ ^ 2) * 58 :=
    mul_le_mul hd4 hC hC0 (by positivity)
  linarith

set_option maxHeartbeats 1000000 in
/-- General form of the gain of `S₃`: slope `z = 1 + κδ` (`0 < κδ ≤ 1/300`). From the polynomial estimate `hQ` at `ρ = ρ_c`
(the expansion in `δ` of `(l₂ − ρl₁) − ρaδl₁`, where `l₁`, `l₂` are the second-order bounds for `log(1+ε)`, `log(1+ρε)`) and `g · 0.6931471808 ≤ G`:
if `h_p ≥ aδq` and `P ≤ q`, then `(1 + ρ_c κδ)^P / (1+κδ)^{L_p} ≤ 2^{−gδ²q}`.
Version 2 of the proof manuscript (revision r6 of the paper) uses `(a, κ, G, g) = (1.23, 10/3, 1.184, 1.708)`, version 3 (revision r7) uses `(1.38, 15/4, 1.52, 2.18)` (`ThmAV3.lean`). -/
lemma C_S3_gainG (a κ G g δ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) (hε1 : κ * δ ≤ 1 / 300) (hg0 : 0 ≤ g)
    (hgG : g * 0.6931471808 ≤ G)
    (hQ : δ ^ 2 * (rhoc * (κ ^ 2 / 2 * (1 - rhoc) - a * κ)) +
      δ ^ 3 * (rhoc * (2 * κ ^ 3 * (rhoc ^ 2 + 1) + a * κ ^ 2 / 2)) +
        δ ^ 4 * (rhoc * (2 * a * κ ^ 3)) ≤ -G * δ ^ 2)
    (P Lq q : ℕ) (hPq : (P : ℝ) ≤ q) (hhp : a * δ * q ≤ lam * Lq - P) :
    (1 + rhoc * ((1 + κ * δ) - 1)) ^ P / (1 + κ * δ) ^ Lq ≤
      (2:ℝ) ^ (-(g * δ ^ 2 * q)) := by
  obtain ⟨hρ1, hρ2⟩ := rhoc_bounds
  set ρ := rhoc with hρ
  set ε := κ * δ with hε
  have hε0 : 0 < ε := by positivity
  have e1 : 1 + ρ * ((1 + ε) - 1) = 1 + ρ * ε := by ring
  rw [e1]
  have hpos1 : 0 < 1 + ρ * ε := by positivity
  have hpos2 : 0 < 1 + ε := by positivity
  have hq0 : (0:ℝ) ≤ q := by positivity
  -- compare logarithms
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num)]
  obtain ⟨_, hl2⟩ := C_log_bounds (ρ * ε) (by positivity) (by nlinarith)
  obtain ⟨hl1, _⟩ := C_log_bounds ε hε0.le (by linarith)
  set l1 := ε - ε ^ 2 / 2 - 2 * ε ^ 3 with hl1def
  set l2 := ρ * ε - (ρ * ε) ^ 2 / 2 + 2 * (ρ * ε) ^ 3 with hl2def
  have hl1pos : 0 ≤ l1 := by
    rw [hl1def]; nlinarith
  have hdiff : 0 ≤ l2 - ρ * l1 := by
    have : l2 - ρ * l1 = ρ * (1 - ρ) * ε ^ 2 / 2 + 2 * ρ * (ρ ^ 2 + 1) * ε ^ 3 := by
      rw [hl1def, hl2def]; ring
    rw [this]
    have : 0 < 1 - ρ := by linarith
    positivity
  -- `L_p = ρ(P + h_p)`
  have hLq : (Lq : ℝ) = ρ * (P + (lam * Lq - P)) := by
    have := C_rhoc_lam
    rw [← hρ] at this
    have e : ρ * (P + (lam * Lq - P)) = (ρ * lam) * Lq := by ring
    rw [e, this, one_mul]
  have hLq0 : (0:ℝ) ≤ Lq := by positivity
  have step1 : (P : ℝ) * Real.log (1 + ρ * ε) - Lq * Real.log (1 + ε) ≤ P * l2 - Lq * l1 := by
    have h1 : (P : ℝ) * Real.log (1 + ρ * ε) ≤ P * l2 := by
      apply mul_le_mul_of_nonneg_left hl2 (by positivity)
    have h2 : (Lq : ℝ) * l1 ≤ Lq * Real.log (1 + ε) := mul_le_mul_of_nonneg_left hl1 hLq0
    linarith
  have step2 : (P : ℝ) * l2 - Lq * l1 ≤ q * (l2 - ρ * l1) - ρ * (a * δ * q) * l1 := by
    rw [hLq]
    have h1 : (P : ℝ) * (l2 - ρ * l1) ≤ q * (l2 - ρ * l1) := mul_le_mul_of_nonneg_right hPq hdiff
    have h2 : ρ * (a * δ * q) * l1 ≤ ρ * (lam * Lq - P) * l1 := by
      apply mul_le_mul_of_nonneg_right _ hl1pos
      apply mul_le_mul_of_nonneg_left hhp (by positivity)
    nlinarith
  -- the polynomial estimate
  have hQ' : (l2 - ρ * l1) - ρ * (a * δ) * l1 ≤ -G * δ ^ 2 := by
    have eQ : (l2 - ρ * l1) - ρ * (a * δ) * l1 =
        δ ^ 2 * (ρ * (κ ^ 2 / 2 * (1 - ρ) - a * κ)) +
          δ ^ 3 * (ρ * (2 * κ ^ 3 * (ρ ^ 2 + 1) + a * κ ^ 2 / 2)) +
            δ ^ 4 * (ρ * (2 * a * κ ^ 3)) := by
      rw [hl1def, hl2def, hε]; ring
    rw [eQ]
    exact hQ
  have hlog2 := Real.log_two_lt_d9
  have hq2 : q * ((l2 - ρ * l1) - ρ * (a * δ) * l1) ≤ q * (-G * δ ^ 2) :=
    mul_le_mul_of_nonneg_left hQ' hq0
  have hfin : (q : ℝ) * (-G * δ ^ 2) ≤ -(g * δ ^ 2 * q) * Real.log 2 := by
    have h0 : 0 ≤ (q : ℝ) * δ ^ 2 := by positivity
    have h1 : g * Real.log 2 ≤ G := by nlinarith
    have e : -(g * δ ^ 2 * q) * Real.log 2 = -((g * Real.log 2) * ((q : ℝ) * δ ^ 2)) := by ring
    rw [e]
    nlinarith
  have e3 : q * (l2 - ρ * l1) - ρ * (a * δ * q) * l1 =
      q * ((l2 - ρ * l1) - ρ * (a * δ) * l1) := by ring
  linarith [step1, step2, e3, hq2, hfin]

set_option maxHeartbeats 1000000 in
/-- The gain of `S₃`: if `h_p ≥ 1.23δq` and `P ≤ q`, then `(1 + ρ_c ε)^P / (1+ε)^{L_p} ≤ 2^{−1.708δ²q}` (`ε = 10δ/3`). -/
lemma C_S3_gain (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) (P Lq q : ℕ) (hPq : (P : ℝ) ≤ q)
    (hhp : 1.23 * δ * q ≤ lam * Lq - P) :
    (1 + rhoc * ((1 + 10 / 3 * δ) - 1)) ^ P / (1 + 10 / 3 * δ) ^ Lq ≤
      (2:ℝ) ^ (-(1.708 * δ ^ 2 * q)) := by
  obtain ⟨hρ1, hρ2⟩ := rhoc_bounds
  have hQ := C_polyQ rhoc δ hρ1 hρ2 hδ hδ1
  refine C_S3_gainG 1.23 (10 / 3) 1.184 1.708 δ hδ (by norm_num) (by linarith) (by norm_num)
    (by norm_num) ?_ P Lq q hPq hhp
  have e : δ ^ 2 * (rhoc * ((10 / 3 : ℝ) ^ 2 / 2 * (1 - rhoc) - 1.23 * (10 / 3))) +
      δ ^ 3 * (rhoc * (2 * (10 / 3 : ℝ) ^ 3 * (rhoc ^ 2 + 1) + 1.23 * (10 / 3) ^ 2 / 2)) +
        δ ^ 4 * (rhoc * (2 * 1.23 * (10 / 3 : ℝ) ^ 3)) =
      δ ^ 2 * (rhoc * (50 / 9 * (1 - rhoc) - 4.1)) +
        δ ^ 3 * (rhoc * (2000 / 27 * (rhoc ^ 2 + 1) + 61.5 / 9)) +
          δ ^ 4 * (rhoc * (2.46 * 1000 / 27)) := by ring
  rw [e]; exact hQ

end Collatz.M1
