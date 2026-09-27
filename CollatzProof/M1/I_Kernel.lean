import CollatzProof.M1.Fourier

/-!
# Auxiliary results for §11: basics of `e(x)`, orthogonality, an upper bound on the Dirichlet kernel, an upper bound on sums of kernels, reindexing sums of periodic functions

Tools used in the proof of `Sstar_bound` (`S11.lean`).
- `I_nd y`: the distance `‖y‖` from `y` to the nearest integer.
- `I_kf x = 1/max(1, 2x)` (`= min(1, 1/(2x))` for `x > 0`). Monotone non-increasing.
- Dirichlet kernel: `‖N^{-1} Σ_{ξ<N} e(yξ)‖ ≤ I_kf(N‖y‖)`.
- Sum of kernels: `Σ_{v<2^q} I_kf(2^q ‖(X − v)/2^q‖) ≤ q + 2` (`q ≥ 4`).
-/

namespace Collatz.M1

open Finset

/-! ## Basics of `e(x)` -/

lemma I_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma I_norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma I_eC_int (n : ℤ) : eC (n : ℝ) = 1 := by
  unfold eC
  have : (2 * Real.pi * Complex.I * ((n : ℝ) : ℂ)) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma I_eC_zero : eC 0 = 1 := by simpa using I_eC_int 0

lemma I_eC_eq_one_iff (x : ℝ) : eC x = 1 ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro h
    unfold eC at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((x : ℂ)) = (n : ℂ) := by
      have := hn
      have e : 2 * ↑Real.pi * Complex.I * (x : ℂ) = (x : ℂ) * (2 * Real.pi * Complex.I) := by ring
      rw [e] at this
      exact mul_right_cancel₀ h2 this
    exact_mod_cast this
  · rintro ⟨n, rfl⟩; exact I_eC_int n

lemma I_eC_pow (x : ℝ) (n : ℕ) : eC x ^ n = eC (n * x) := by
  unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma I_conj_eC (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

lemma I_eC_ne_zero (x : ℝ) : eC x ≠ 0 := by unfold eC; exact Complex.exp_ne_zero _

/-! ## Orthogonality -/

/-- `Σ_{j<N} e(jm/N) = N·1[N ∣ m]`. -/
lemma I_sum_eC_range (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ j ∈ range N, eC ((j : ℝ) * m / N) = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : ∀ j : ℕ, eC ((j : ℝ) * m / N) = eC ((m : ℝ) / N) ^ j := by
    intro j; rw [I_eC_pow]; congr 1; ring
  simp_rw [hpow]
  split_ifs with hd
  · obtain ⟨k, hk⟩ := hd
    have : eC ((m : ℝ) / N) = 1 := by
      rw [hk]; push_cast
      rw [show (N : ℝ) * k / N = (k : ℝ) by field_simp]
      exact I_eC_int k
    simp [this]
  · have hne : eC ((m : ℝ) / N) ≠ 1 := by
      intro h
      rw [I_eC_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      apply hd
      refine ⟨k, ?_⟩
      have : (m : ℝ) = N * k := by rw [← hk]; field_simp
      exact_mod_cast this
    rw [geom_sum_eq hne, I_eC_pow]
    rw [show (N : ℝ) * ((m : ℝ) / N) = (m : ℝ) by field_simp, I_eC_int]
    simp

/-! ## Distance to the nearest integer -/

/-- `‖y‖ = |y − round y|`. -/
noncomputable def I_nd (y : ℝ) : ℝ := |y - round y|

lemma I_nd_nonneg (y : ℝ) : 0 ≤ I_nd y := abs_nonneg _

lemma I_nd_le (y : ℝ) (z : ℤ) : I_nd y ≤ |y - z| := round_le y z

lemma I_nd_le_half (y : ℝ) : I_nd y ≤ 1 / 2 := abs_sub_round y

lemma I_le_nd (y δ : ℝ) (h : ∀ z : ℤ, δ ≤ |y - z|) : δ ≤ I_nd y := h _

lemma I_nd_add_le (y t : ℝ) : I_nd y ≤ I_nd (y + t) + |t| := by
  calc I_nd y ≤ |y - (round (y + t) : ℤ)| := I_nd_le y _
    _ = |(y + t - round (y + t)) + (-t)| := by ring_nf
    _ ≤ |y + t - round (y + t)| + |-t| := abs_add_le _ _
    _ = I_nd (y + t) + |t| := by rw [abs_neg]; rfl

lemma I_nd_add_int (y : ℝ) (n : ℤ) : I_nd (y + n) = I_nd y := by
  apply le_antisymm
  · calc I_nd (y + n) ≤ |y + n - ((round y + n : ℤ) : ℝ)| := I_nd_le _ _
      _ = I_nd y := by unfold I_nd; push_cast; ring_nf
  · calc I_nd y ≤ |y - ((round (y + n) - n : ℤ) : ℝ)| := I_nd_le _ _
      _ = I_nd (y + n) := by unfold I_nd; push_cast; ring_nf

lemma I_nd_neg (y : ℝ) : I_nd (-y) = I_nd y := by
  apply le_antisymm
  · calc I_nd (-y) ≤ |-y - ((-round y : ℤ) : ℝ)| := I_nd_le _ _
      _ = I_nd y := by unfold I_nd; push_cast; rw [← abs_neg]; ring_nf
  · calc I_nd y ≤ |y - ((-round (-y) : ℤ) : ℝ)| := I_nd_le _ _
      _ = I_nd (-y) := by unfold I_nd; push_cast; rw [← abs_neg]; ring_nf

/-! ## `I_kf` -/

/-- `I_kf x = 1/max(1, 2x)`. -/
noncomputable def I_kf (x : ℝ) : ℝ := 1 / max 1 (2 * x)

lemma I_kf_pos (x : ℝ) : 0 < I_kf x := by
  unfold I_kf; apply div_pos one_pos; exact lt_of_lt_of_le one_pos (le_max_left _ _)

lemma I_kf_nonneg (x : ℝ) : 0 ≤ I_kf x := (I_kf_pos x).le

lemma I_kf_le_one (x : ℝ) : I_kf x ≤ 1 := by
  unfold I_kf; rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]; exact le_max_left _ _

lemma I_kf_le_inv (x : ℝ) (hx : 0 < x) : I_kf x ≤ 1 / (2 * x) := by
  unfold I_kf
  apply one_div_le_one_div_of_le (by positivity) (le_max_right _ _)

lemma I_kf_anti : Antitone I_kf := by
  intro x y hxy
  unfold I_kf
  apply one_div_le_one_div_of_le (lt_of_lt_of_le one_pos (le_max_left _ _))
  exact max_le_max le_rfl (by linarith)

/-- If `‖X‖ ≤ 1` and `‖X‖ ≤ 1/(2t)` (`t > 0`), then `‖X‖ ≤ I_kf t`. -/
lemma I_le_kf (a t : ℝ) (h1 : a ≤ 1) (h2 : 0 < t → a ≤ 1 / (2 * t)) : a ≤ I_kf t := by
  unfold I_kf
  rcases le_total 1 (2 * t) with h | h
  · rw [max_eq_right h]
    have ht : 0 < t := by linarith
    simpa using h2 ht
  · rw [max_eq_left h]; simpa using h1

/-! ## Dirichlet kernel -/

/-- `|sin(πy)| ≥ 2‖y‖`. -/
lemma I_abs_sin_ge (y : ℝ) : 2 * I_nd y ≤ |Real.sin (Real.pi * y)| := by
  set t := y - round y with ht
  have hy : Real.pi * y = Real.pi * t + (round y : ℤ) * Real.pi := by rw [ht]; ring
  rw [hy, Real.sin_add_int_mul_pi, abs_mul]
  have h1 : |((-1 : ℝ) ^ (round y))| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [h1, one_mul]
  have hnd : I_nd y = |t| := rfl
  rw [hnd]
  have hth : |t| ≤ 1 / 2 := abs_sub_round y
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0]
    have hs := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by
      have := abs_of_nonneg h0 ▸ hth; nlinarith [Real.pi_pos])
    have : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rw [this] at hs
    exact le_trans hs (le_abs_self _)
  · rw [abs_of_nonpos h0]
    have hs := Real.mul_le_sin (x := Real.pi * (-t)) (by nlinarith [Real.pi_pos]) (by
      have := abs_of_nonpos h0 ▸ hth; nlinarith [Real.pi_pos])
    have : 2 / Real.pi * (Real.pi * (-t)) = 2 * (-t) := by field_simp
    rw [this] at hs
    rw [show Real.pi * t = -(Real.pi * (-t)) by ring, Real.sin_neg, abs_neg]
    exact le_trans hs (le_abs_self _)

/-- `‖e(y) − 1‖ ≥ 4‖y‖`. -/
lemma I_norm_eC_sub_one (y : ℝ) : 4 * I_nd y ≤ ‖eC y - 1‖ := by
  have : eC y = Complex.exp (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) := by
    unfold eC; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * y) / 2 = Real.pi * y by ring]
  rw [Real.norm_eq_abs, abs_mul]
  have := I_abs_sin_ge y
  norm_num
  linarith

/-- Upper bound on the Dirichlet kernel: `‖N^{-1} Σ_{ξ<N} e(yξ)‖ ≤ I_kf(N‖y‖)`. -/
lemma I_dirichlet (N : ℕ) (hN : 0 < N) (y : ℝ) :
    ‖(N : ℂ)⁻¹ * ∑ ξ ∈ range N, eC (y * ξ)‖ ≤ I_kf (N * I_nd y) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum_le : ‖∑ ξ ∈ range N, eC (y * ξ)‖ ≤ N := by
    calc ‖∑ ξ ∈ range N, eC (y * ξ)‖ ≤ ∑ ξ ∈ range N, ‖eC (y * ξ)‖ := norm_sum_le _ _
      _ = N := by simp [I_norm_eC]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply I_le_kf
  · rw [inv_mul_le_iff₀ hNr]; linarith
  · intro ht
    have hnd : 0 < I_nd y := by
      by_contra h; push Not at h; nlinarith [I_nd_nonneg y]
    have hne : eC y ≠ 1 := by
      intro h
      rw [I_eC_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have : I_nd y = 0 := by
        apply le_antisymm _ (I_nd_nonneg y)
        calc I_nd y ≤ |y - n| := I_nd_le y n
          _ = 0 := by rw [hn]; simp
      linarith
    have hpow : ∀ ξ : ℕ, eC (y * ξ) = eC y ^ ξ := by
      intro ξ; rw [I_eC_pow]; congr 1; ring
    simp_rw [hpow]
    rw [geom_sum_eq hne, norm_div]
    have hden : 4 * I_nd y ≤ ‖eC y - 1‖ := I_norm_eC_sub_one y
    have hnum : ‖eC y ^ N - 1‖ ≤ 2 := by
      calc ‖eC y ^ N - 1‖ ≤ ‖eC y ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, I_norm_eC]; norm_num
    have hdpos : 0 < ‖eC y - 1‖ := by linarith
    calc (N : ℝ)⁻¹ * (‖eC y ^ N - 1‖ / ‖eC y - 1‖) ≤ (N : ℝ)⁻¹ * (2 / (4 * I_nd y)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ‖eC y ^ N - 1‖ / ‖eC y - 1‖ ≤ 2 / ‖eC y - 1‖ :=
                div_le_div_of_nonneg_right hnum hdpos.le
            _ ≤ 2 / (4 * I_nd y) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = 1 / (2 * (N * I_nd y)) := by field_simp; ring

/-! ## Reindexing sums of periodic functions, splitting by parity -/

/-- For a function `F : ℤ → M` of period `N` and `u` coprime to `N`, `Σ_{x<N} F(ux + e) = Σ_{x<N} F(x)`. -/
lemma I_sum_affine {M : Type*} [AddCommMonoid M] (N : ℕ) (hN : 0 < N) (F : ℤ → M)
    (hF : ∀ x, F (x + N) = F x) (u e : ℤ) (hu : IsCoprime u (N : ℤ)) :
    ∑ x ∈ range N, F (u * x + e) = ∑ x ∈ range N, F x := by
  have hper : Function.Periodic F (N : ℤ) := fun x => hF x
  have hmod : ∀ x : ℤ, F x = F (x % N) := by
    intro x
    have h := hper.int_mul (x / N) (x % N)
    rw [← h]; congr 1
    rw [Int.cast_id]
    have := Int.emod_add_mul_ediv x N
    linarith [this, mul_comm (x / (N : ℤ)) (N : ℤ)]
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  let i : ℕ → ℕ := fun x => ((u * x + e) % N).toNat
  have hi_lt : ∀ x, i x < N := by
    intro x
    have h1 := Int.emod_nonneg (u * x + e) hNz.ne'
    have h2 := Int.emod_lt_of_pos (u * x + e) hNz
    simp only [i]; omega
  have hi_cast : ∀ x, ((i x : ℕ) : ℤ) = (u * x + e) % N := by
    intro x
    have h1 := Int.emod_nonneg (u * x + e) hNz.ne'
    simp only [i]; exact Int.toNat_of_nonneg h1
  have hinj : Set.InjOn i (range N : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h : (u * a + e) % N = (u * b + e) % N := by rw [← hi_cast, ← hi_cast, hab]
    have hd : (N : ℤ) ∣ u * ((a : ℤ) - b) := by
      have := Int.emod_emod_of_dvd (u * a + e) (dvd_refl (N : ℤ))
      have h' := Int.ModEq.dvd (h.symm : (u * b + e) ≡ (u * a + e) [ZMOD N])
      have : u * ((a : ℤ) - b) = (u * a + e) - (u * b + e) := by ring
      rw [this]; exact h'
    have hd2 : (N : ℤ) ∣ (a : ℤ) - b := hu.symm.dvd_of_dvd_mul_left hd
    obtain ⟨k, hk⟩ := hd2
    have : k = 0 := by
      by_contra hk0
      rcases lt_or_gt_of_ne hk0 with h | h
      · have : (N : ℤ) * k ≤ -N := by nlinarith
        omega
      · have : (N : ℤ) * k ≥ N := by nlinarith
        omega
    subst this; omega
  rw [Finset.sum_nbij i (fun x _ => mem_range.mpr (hi_lt x)) hinj ?_ ?_]
  · intro b hb
    have := Finset.surj_on_of_inj_on_of_card_le (s := range N) (t := range N) (fun a _ => i a)
      (fun a _ => mem_range.mpr (hi_lt a)) (fun a b ha hb h => hinj ha hb h) le_rfl b hb
    obtain ⟨a, ha, rfl⟩ := this
    exact ⟨a, ha, rfl⟩
  · intro x _
    rw [hmod (u * x + e), hi_cast]

/-- Translated version. -/
lemma I_sum_shift {M : Type*} [AddCommMonoid M] (N : ℕ) (hN : 0 < N) (F : ℤ → M)
    (hF : ∀ x, F (x + N) = F x) (e : ℤ) :
    ∑ x ∈ range N, F (x + e) = ∑ x ∈ range N, F x := by
  have := I_sum_affine N hN F hF 1 e isCoprime_one_left
  simpa using this

/-- `Σ_{x<2N} f(x) = Σ_{x<N} f(2x) + Σ_{x<N} f(2x+1)`. -/
lemma I_sum_range_two_mul {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ x ∈ range (2 * N), f x = ∑ x ∈ range N, f (2 * x) + ∑ x ∈ range N, f (2 * x + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    rw [show 2 * n + 1 = 2 * n + 1 from rfl]
    abel

/-! ## Upper bound on sums of kernels -/

/-- If `y ∈ [0,1)` and `2 ≤ k < N`, then `|y − k − Nz| ≥ min(k−1, N−k)` for every integer `z`. -/
lemma I_dist_lower (N k : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) (hk2 : 2 ≤ k) (hkN : k < N) (z : ℤ) :
    min ((k : ℝ) - 1) ((N : ℝ) - k) ≤ |y - k - N * z| := by
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  rcases le_or_gt 0 z with hz | hz
  · have h1 : (0 : ℝ) ≤ (N : ℝ) * z := by positivity
    have : y - k - N * z < 0 := by linarith
    rw [abs_of_neg this]
    exact le_trans (min_le_left _ _) (by linarith)
  · have hz' : z ≤ -1 := by omega
    have h1 : (N : ℝ) * z ≤ -N := by
      have : (z : ℝ) ≤ -1 := by exact_mod_cast hz'
      nlinarith [show (0 : ℝ) ≤ N by positivity]
    have hk : (k : ℝ) < N := by exact_mod_cast hkN
    have : 0 ≤ y - k - N * z := by linarith
    rw [abs_of_nonneg this]
    exact le_trans (min_le_right _ _) (by linarith)

lemma I_harmonic_le (n : ℕ) : ∑ m ∈ range n, (1 : ℝ) / (m + 1) ≤ 1 + Real.log n := by
  have := harmonic_le_one_add_log n
  have h : ((harmonic n : ℚ) : ℝ) = ∑ m ∈ range n, (1 : ℝ) / (m + 1) := by
    unfold harmonic; push_cast; simp [one_div]
  rw [← h]; exact this

/-- Sum of kernels: if `q ≥ 4`, then `Σ_{v<2^q} I_kf(2^q‖(X − v)/2^q‖) ≤ q + 2`. -/
lemma I_kernel_sum (q : ℕ) (hq : 4 ≤ q) (X : ℝ) :
    ∑ v ∈ range (2 ^ q), I_kf (2 ^ q * I_nd ((X - v) / 2 ^ q)) ≤ q + 2 := by
  set N : ℕ := 2 ^ q with hN
  have hNpos : 0 < N := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN4 : 16 ≤ N := by
    have : 2 ^ 4 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    simpa [hN] using this
  have hcastN : ((2 : ℝ) ^ q) = (N : ℝ) := by simp [hN]
  -- write it as a function on the integers
  set F : ℤ → ℝ := fun v => I_kf (N * I_nd ((X - v) / N)) with hF
  have hFper : ∀ v, F (v + N) = F v := by
    intro v
    simp only [hF]
    congr 2
    have : (X - ((v + N : ℤ) : ℝ)) / N = (X - v) / N + ((-1 : ℤ) : ℝ) := by
      push_cast; field_simp; ring
    rw [this, I_nd_add_int]
  have hsum : ∑ v ∈ range (2 ^ q), I_kf (2 ^ q * I_nd ((X - v) / 2 ^ q)) =
      ∑ v ∈ range N, F v := by
    rw [hcastN]; simp [hF]; rfl
  rw [hsum]
  set m0 : ℤ := ⌊X⌋ with hm0
  set y : ℝ := X - m0 with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith [Int.floor_le X]
  have hy1 : y < 1 := by rw [hy]; linarith [Int.lt_floor_add_one X]
  rw [← I_sum_shift N hNpos F hFper m0]
  have hG : ∀ k : ℕ, F (k + m0) = I_kf (N * I_nd ((y - k) / N)) := by
    intro k; simp only [hF]; congr 3; push_cast; rw [hy]; ring
  simp_rw [hG]
  -- bound for each term
  have hbd : ∀ k ∈ range N, I_kf (N * I_nd ((y - k) / N)) ≤
      (if k < 2 then 1 else 1 / (2 * ((k : ℝ) - 1)) + 1 / (2 * ((N : ℝ) - k))) := by
    intro k hk
    rw [mem_range] at hk
    split_ifs with h2
    · exact I_kf_le_one _
    · push Not at h2
      have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast h2
        linarith
      have hk2 : (1 : ℝ) ≤ (N : ℝ) - k := by
        have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
        linarith
      set μ := min ((k : ℝ) - 1) ((N : ℝ) - k) with hμ
      have hμpos : 0 < μ := lt_of_lt_of_le one_pos (le_min hk1 hk2)
      have hlow : μ ≤ N * I_nd ((y - k) / N) := by
        have : μ / N ≤ I_nd ((y - k) / N) := by
          apply I_le_nd
          intro z
          have := I_dist_lower N k y hy0 hy1 h2 hk z
          rw [div_le_iff₀ hNr]
          calc μ ≤ |y - k - N * z| := this
            _ = |(y - k) / N - z| * N := by
              rw [← abs_of_pos hNr, ← abs_mul, abs_of_pos hNr]; congr 1; field_simp
        rw [div_le_iff₀ hNr] at this; linarith
      calc I_kf (N * I_nd ((y - k) / N)) ≤ I_kf μ := I_kf_anti hlow
        _ ≤ 1 / (2 * μ) := I_kf_le_inv μ hμpos
        _ ≤ 1 / (2 * ((k : ℝ) - 1)) + 1 / (2 * ((N : ℝ) - k)) := by
          rcases le_total ((k : ℝ) - 1) ((N : ℝ) - k) with h | h
          · rw [hμ, min_eq_left h]
            have : 0 ≤ 1 / (2 * ((N : ℝ) - k)) := by positivity
            linarith
          · rw [hμ, min_eq_right h]
            have : 0 ≤ 1 / (2 * ((k : ℝ) - 1)) := by positivity
            linarith
  refine le_trans (sum_le_sum hbd) ?_
  -- sum of the bounds
  have hsplit : ∑ k ∈ range N, (if k < 2 then (1 : ℝ) else
      1 / (2 * ((k : ℝ) - 1)) + 1 / (2 * ((N : ℝ) - k))) =
      2 + ∑ k ∈ Ico 2 N, (1 / (2 * ((k : ℝ) - 1)) + 1 / (2 * ((N : ℝ) - k))) := by
    rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (show 0 ≤ 2 by norm_num)
      (show 2 ≤ N by omega)]
    congr 1
    · simp [Finset.sum_range_succ]; norm_num
    · apply sum_congr rfl
      intro k hk; rw [mem_Ico] at hk
      rw [ite_eq_right_iff.mpr (by intro h; omega)]
  rw [hsplit, sum_add_distrib]
  have hA : ∑ k ∈ Ico 2 N, 1 / (2 * ((k : ℝ) - 1)) =
      (1 / 2) * ∑ m ∈ range (N - 2), (1 : ℝ) / (m + 1) := by
    rw [Finset.sum_Ico_eq_sum_range, mul_sum]
    apply sum_congr rfl; intro m _; push_cast
    rw [show (2 : ℝ) + m - 1 = m + 1 by ring, one_div_mul_one_div]
  have hB : ∑ k ∈ Ico 2 N, 1 / (2 * ((N : ℝ) - k)) =
      (1 / 2) * ∑ m ∈ range (N - 2), (1 : ℝ) / (m + 1) := by
    rw [Finset.sum_Ico_eq_sum_range, mul_sum]
    rw [← Finset.sum_range_reflect]
    apply sum_congr rfl; intro m hm; rw [mem_range] at hm
    have : ((2 + (N - 2 - 1 - m) : ℕ) : ℝ) = (N : ℝ) - 1 - m := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    rw [this, show (N : ℝ) - ((N : ℝ) - 1 - m) = m + 1 by ring, one_div_mul_one_div]
  rw [hA, hB]
  have hH := I_harmonic_le (N - 2)
  have hlog : Real.log ((N - 2 : ℕ) : ℝ) ≤ q * Real.log 2 := by
    have h1 : ((N - 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 2
    have h2 : (0 : ℝ) < ((N - 2 : ℕ) : ℝ) := by
      have : 0 < N - 2 := by omega
      exact_mod_cast this
    calc Real.log ((N - 2 : ℕ) : ℝ) ≤ Real.log N := Real.log_le_log h2 h1
      _ = q * Real.log 2 := by rw [hN]; push_cast; rw [Real.log_pow]
  have hl2 := Real.log_two_lt_d9
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith

end Collatz.M1
