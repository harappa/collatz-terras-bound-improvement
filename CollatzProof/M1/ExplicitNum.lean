import CollatzProof.M1.K_Anal

/-!
# Explicit values of the main theorem, version 2 of the proof manuscript (revision r6 of the paper): numerical estimates

With the constants `p = 312`, `c_D = 9×10^{−4}`, `ρ♯ = ρ_c + 10^{−4}` of §14.1 of version 2 of the proof manuscript (the constants of revision r6 of the paper), we prove
the numerical inequalities used by the assembly of Proposition 14.1 (`ExplicitCore.lean`). Each is reduced to a comparison of rational numbers (`norm_num`).
- `r_c^{312} ≤ 1.6×10^{−5}` (used together with `log(1 + x) ≤ x`, instead of `log₂(1 + r_c^p) ≤ 0.025c_D` of the manuscript).
- `((1 + r_c)/2)^{312} ≤ 1/4` (the second half of Lemma 14.0 (g), for `p = 312`).
- `1 − φ_{312} ≥ 0.0033` (a sharpening of `1 − φ_p ≥ 1/p` of Lemma 14.0 (a) for `p = 312`; from `e^{−u} ≤ 1 − u + u²` and Bernoulli's inequality).
- `w = ρ♯(1 − ρ♯) ∈ [0.2328, 1/4]`.
-/

namespace Collatz.M1

/-- `r_c^{312} ≤ 1.6×10^{−5}` (`r_c < 0.9652`). -/
lemma X_rc_pow312 : rc ^ 312 ≤ 1.6e-5 := by
  obtain ⟨h1, h2⟩ := rc_bounds
  calc rc ^ 312 ≤ (0.9652:ℝ) ^ 312 := pow_le_pow_left₀ (by linarith) h2.le 312
    _ ≤ 1.6e-5 := by
        set_option exponentiation.threshold 400 in norm_num

/-- `((1 + r_c)/2)^{312} ≤ 1/4`. -/
lemma X_bp312 : ((1 + rc) / 2) ^ 312 ≤ 1/4 := by
  obtain ⟨h1, h2⟩ := rc_bounds
  calc ((1 + rc) / 2) ^ 312 ≤ ((1 + 0.9652) / 2 : ℝ) ^ 312 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 312
    _ ≤ 1/4 := by
        set_option exponentiation.threshold 400 in norm_num

/-- `e^{−u} ≤ 1 − u + u²` (`0 ≤ u ≤ 1`). -/
lemma X_exp_neg_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : Real.exp (-u) ≤ 1 - u + u ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -u) (by rw [abs_neg, abs_of_nonneg hu0]; exact hu1)
  have := (abs_le.1 h).2
  rw [neg_sq] at this
  linarith

/-- `φ_{312} ≤ 1 − 0.0033` (`1 − φ_{312} ≈ 1.0378/312`). -/
lemma X_phi312 : phiP ((312:ℕ):ℝ) ≤ 1 - 0.0033 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  set x : ℝ := 1 / 311 with hx
  have hx0 : 0 < x := by rw [hx]; norm_num
  have hr : ((312:ℕ):ℝ) / (((312:ℕ):ℝ) - 1) = 1 + x := by rw [hx]; norm_num
  unfold phiP
  rw [hr]
  -- y = 2^{−(1+x)} + 2^{1−2(1+x)} = (2^{−x} + 2^{−2x})/2
  set u : ℝ := x * Real.log 2 with hu
  have hu1 : 0.00222 ≤ u := by rw [hu, hx]; nlinarith
  have hu2 : u ≤ 0.00223 := by rw [hu, hx]; nlinarith
  have e1 : (2:ℝ) ^ (-(1 + x)) = (1/2) * Real.exp (-u) := by
    rw [show -(1 + x) = -1 + (-x) by ring, Real.rpow_add (by norm_num), Real.rpow_neg_one,
      Real.rpow_def_of_pos (by norm_num), hu]
    ring_nf
  have e2 : (2:ℝ) ^ (1 - 2 * (1 + x)) = (1/2) * Real.exp (-(2 * u)) := by
    rw [show 1 - 2 * (1 + x) = -1 + (-2 * x) by ring, Real.rpow_add (by norm_num), Real.rpow_neg_one,
      Real.rpow_def_of_pos (by norm_num), hu]
    ring_nf
  have b1 := X_exp_neg_le u (by linarith) (by linarith)
  have b2 := X_exp_neg_le (2 * u) (by linarith) (by linarith)
  set y : ℝ := (2:ℝ) ^ (-(1 + x)) + (2:ℝ) ^ (1 - 2 * (1 + x)) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyle : y ≤ 1 - 1.5 * u + 2.5 * u ^ 2 := by
    rw [hy, e1, e2]; nlinarith
  have hinv0 : 0 ≤ 1 / (1 + x) := by positivity
  have hinv1 : 1 / (1 + x) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hbern := _root_.rpow_one_add_le_one_add_mul_self (s := y - 1) (by linarith) hinv0 hinv1
  rw [show 1 + (y - 1) = y by ring] at hbern
  have hinv : 1 / (1 + x) = 311 / 312 := by rw [hx]; norm_num
  rw [hinv] at hbern
  have hkey : y - 1 ≤ -(1.5 * u - 2.5 * u ^ 2) := by linarith
  have hq : 0.00331 ≤ 1.5 * u - 2.5 * u ^ 2 := by nlinarith
  nlinarith

/-- For `ρ♯ = ρ_c + 10^{−4}`: `w = ρ♯(1 − ρ♯) ∈ [0.2328, 1/4]`. -/
lemma X_w_bounds : 0.2328 ≤ (rhoc + 1e-4) * (1 - (rhoc + 1e-4)) ∧
    (rhoc + 1e-4) * (1 - (rhoc + 1e-4)) ≤ 1/4 := by
  obtain ⟨h1, h2⟩ := rhoc_bounds
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h1.le) (sub_nonneg.2 h2.le)]
  · nlinarith [sq_nonneg (rhoc + 1e-4 - 1/2)]

/-- `Θ_{φ_{312}}(ρ♯) ≤ 1 − 0.0066·0.2328`. -/
lemma X_theta_phi312 : Theta (phiP ((312:ℕ):ℝ)) (rhoc + 1e-4) ≤ 1 - 0.0066 * 0.2328 := by
  have hφ := X_phi312
  obtain ⟨hw1, -⟩ := X_w_bounds
  have e : Theta (phiP ((312:ℕ):ℝ)) (rhoc + 1e-4) =
      1 - 2 * (1 - phiP ((312:ℕ):ℝ)) * ((rhoc + 1e-4) * (1 - (rhoc + 1e-4))) := by
    unfold Theta; ring
  rw [e]
  have h1 : 0.0066 ≤ 2 * (1 - phiP ((312:ℕ):ℝ)) := by linarith
  nlinarith

end Collatz.M1
