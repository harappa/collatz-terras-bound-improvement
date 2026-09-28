import CollatzProof.M1.ExplicitNum

/-!
# Explicit values of version 3 of the proof manuscript (revision r7 of the paper): numerical estimates (`p = 247`)

With the constants `c_D = 9×10^{−3}`, `p = 247`, `ρ♯ = ρ_c + 10^{−4}` of §14.6 of version 3 of the proof manuscript (Section 16.1 of the paper), we prove
the numerical inequalities used by the assembly of Proposition 14.1 (`ExplicitV3.lean`). As in `ExplicitNum.lean` (v2, `p = 312`),
each is reduced to a comparison of rational numbers (`norm_num`).
- `r_c^{247} ≤ 1.6×10^{−4}` (`r_c < 0.9652`; the true value is about `1.549×10^{−4}`).
- `((1 + r_c)/2)^{247} ≤ 1/4` (the second half of Lemma 14.0 (g)).
- `1 − φ_{247} ≥ 0.004189` (the true value is about `0.0041996`; from `e^{−u} ≤ 1 − u + u²` and Bernoulli's inequality).
- `Θ_{φ_{247}}(ρ♯) ≤ 1 − v` with `v = 0.008378·0.2328 = 1.9504×10^{−3}` (the true value is about `1.9556×10^{−3}`).

**Precision**: in v3 the margin of `κ_eff` is small, about `0.05𝔅`. The rate condition of the third term of Proposition 14.1 (`X_rate3G`:
`(E + δ') log 2 + R/p < c_D v/2`) has, with the `v` and `R` here, left-hand side `8.4204×10^{−6}` and right-hand side `8.7768×10^{−6}` (a margin of about 4%).
-/

namespace Collatz.M1

/-- `r_c^{247} ≤ 1.6×10^{−4}` (`r_c < 0.9652`). -/
lemma X_rc_pow247 : rc ^ 247 ≤ 1.6e-4 := by
  obtain ⟨h1, h2⟩ := rc_bounds
  calc rc ^ 247 ≤ (0.9652:ℝ) ^ 247 := pow_le_pow_left₀ (by linarith) h2.le 247
    _ ≤ 1.6e-4 := by
        set_option exponentiation.threshold 400 in norm_num

/-- `((1 + r_c)/2)^{247} ≤ 1/4`. -/
lemma X_bp247 : ((1 + rc) / 2) ^ 247 ≤ 1/4 := by
  obtain ⟨h1, h2⟩ := rc_bounds
  calc ((1 + rc) / 2) ^ 247 ≤ ((1 + 0.9652) / 2 : ℝ) ^ 247 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 247
    _ ≤ 1/4 := by
        set_option exponentiation.threshold 400 in norm_num

/-- `φ_{247} ≤ 1 − 0.004189` (`1 − φ_{247} ≈ 0.0041996`). The same proof as `X_phi312`, with `x = 1/246`. -/
lemma X_phi247 : phiP ((247:ℕ):ℝ) ≤ 1 - 0.004189 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  set x : ℝ := 1 / 246 with hx
  have hx0 : 0 < x := by rw [hx]; norm_num
  have hr : ((247:ℕ):ℝ) / (((247:ℕ):ℝ) - 1) = 1 + x := by rw [hx]; norm_num
  unfold phiP
  rw [hr]
  -- y = 2^{−(1+x)} + 2^{1−2(1+x)} = (2^{−x} + 2^{−2x})/2
  set u : ℝ := x * Real.log 2 with hu
  have hu1 : 0.0028176 ≤ u := by rw [hu, hx]; nlinarith
  have hu2 : u ≤ 0.0028177 := by rw [hu, hx]; nlinarith
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
  have hinv : 1 / (1 + x) = 246 / 247 := by rw [hx]; norm_num
  rw [hinv] at hbern
  have hkey : y - 1 ≤ -(1.5 * u - 2.5 * u ^ 2) := by linarith
  have hq : 0.0042065 ≤ 1.5 * u - 2.5 * u ^ 2 := by nlinarith
  nlinarith

/-- `Θ_{φ_{247}}(ρ♯) ≤ 1 − 0.008378·0.2328` (`ρ♯ = ρ_c + 10^{−4}`, `2(1 − φ_{247}) ≥ 0.008378`, `w ≥ 0.2328`). -/
lemma X_theta_phi247 : Theta (phiP ((247:ℕ):ℝ)) (rhoc + 1e-4) ≤ 1 - 0.008378 * 0.2328 := by
  have hφ := X_phi247
  obtain ⟨hw1, -⟩ := X_w_bounds
  have e : Theta (phiP ((247:ℕ):ℝ)) (rhoc + 1e-4) =
      1 - 2 * (1 - phiP ((247:ℕ):ℝ)) * ((rhoc + 1e-4) * (1 - (rhoc + 1e-4))) := by
    unfold Theta; ring
  rw [e]
  have h1 : 0.008378 ≤ 2 * (1 - phiP ((247:ℕ):ℝ)) := by linarith
  nlinarith

end Collatz.M1
