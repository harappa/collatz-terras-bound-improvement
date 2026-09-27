import CollatzProof.M1.Counting

/-!
# Auxiliary results for Theorem B: Fourier-analytic components

Basic properties of `e(x)`, orthogonality, Parseval, the estimate of the coefficients `ω` of Lemma 5.1, and periodic sums over shells.
The prefix `D_` marks auxiliary declarations for Theorem B.
-/

namespace Collatz.M1

open Finset

/-! ## Basic properties of `e(x)` -/

lemma D_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; push_cast; ring_nf

lemma D_eC_int (n : ℤ) : eC n = 1 := by
  unfold eC
  have : 2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = n * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma D_eC_add_int (x : ℝ) (n : ℤ) : eC (x + n) = eC x := by
  rw [D_eC_add, D_eC_int, mul_one]

lemma D_norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma D_eC_nat_mul (n : ℕ) (x : ℝ) : eC (n * x) = eC x ^ n := by
  unfold eC; rw [← Complex.exp_nat_mul]; push_cast; ring_nf

lemma D_eC_zero : eC 0 = 1 := by simp [eC]

/-- `‖e(β) − 1‖ = 2|sin πβ|`. -/
lemma D_norm_eC_sub_one (β : ℝ) : ‖eC β - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
  unfold eC
  have : 2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) = Complex.I * ((2 * Real.pi * β : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  rw [show 2 * Real.pi * β / 2 = Real.pi * β by ring]

/-- `‖(1 + e(y))/2‖² = cos²(πy)`. -/
lemma D_norm_one_add_eC_sq (y : ℝ) : ‖(1 + eC y) / 2‖ ^ 2 = Real.cos (Real.pi * y) ^ 2 := by
  have h : (1 + eC y) / 2 = eC (y / 2) * ((Real.cos (Real.pi * y) : ℝ) : ℂ) := by
    unfold eC
    rw [Complex.ofReal_cos, Complex.cos]
    rw [mul_div_assoc', mul_add, ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
    rw [Complex.exp_zero]; ring
  rw [h, norm_mul, D_norm_eC, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Orthogonality and Parseval -/

/-- `Σ_{h<n} e(ha/n) = n·1[n ∣ a]`. -/
lemma D_sum_eC_range (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ∑ h ∈ range n, eC ((h : ℝ) * a / n) = if (n : ℤ) ∣ a then (n : ℂ) else 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  split_ifs with hd
  · obtain ⟨b, rfl⟩ := hd
    have : ∀ h ∈ range n, eC ((h : ℝ) * ((n * b : ℤ) : ℝ) / n) = 1 := by
      intro h _
      have : (h : ℝ) * ((n * b : ℤ) : ℝ) / n = ((h * b : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [this, D_eC_int]
    rw [sum_congr rfl this]; simp
  · set r := eC (a / n) with hr
    have hpow : ∀ h : ℕ, eC ((h : ℝ) * a / n) = r ^ h := by
      intro h; rw [hr, ← D_eC_nat_mul]; ring_nf
    simp_rw [hpow]
    have hr1 : r ≠ 1 := by
      intro h1
      rw [hr, eC, Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have h2 : ((a / n : ℝ) : ℂ) = (m : ℂ) := by
        have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ hI; rw [hm]; ring
      have h3 : (a / n : ℝ) = m := by exact_mod_cast h2
      apply hd
      refine ⟨m, ?_⟩
      have : (a : ℝ) = n * m := by field_simp at h3; linarith
      exact_mod_cast this
    rw [geom_sum_eq hr1]
    have : r ^ n = 1 := by
      rw [hr, ← D_eC_nat_mul]
      have : (n : ℝ) * (a / n) = (a : ℤ) := by field_simp
      rw [this, D_eC_int]
    rw [this]; simp

/-- Parseval: if `E ⊂ [0, 2^q)` then `Σ_{ξ<2^q} |Ê(ξ)|² = 2^q |E|`. -/
lemma D_parseval (q : ℕ) (E : Finset ℕ) (hE : E ⊆ range (2 ^ q)) :
    ∑ ξ ∈ range (2 ^ q), ‖Ehat q E ξ‖ ^ 2 = (2:ℝ) ^ q * E.card := by
  have hQ : 0 < 2 ^ q := by positivity
  have key : ∀ ξ : ℕ, ((‖Ehat q E ξ‖ ^ 2 : ℝ) : ℂ) =
      ∑ z ∈ E, ∑ z' ∈ E, eC ((ξ : ℝ) * ((z' : ℤ) - z : ℤ) / (2 ^ q : ℕ)) := by
    intro ξ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Ehat, map_sum, sum_mul_sum]
    apply sum_congr rfl; intro z _; apply sum_congr rfl; intro z' _
    unfold eC
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat]
    ring
  have h2 : ((∑ ξ ∈ range (2 ^ q), ‖Ehat q E ξ‖ ^ 2 : ℝ) : ℂ) = ((2:ℝ) ^ q * E.card : ℝ) := by
    rw [Complex.ofReal_sum, sum_congr rfl (fun ξ _ => key ξ), sum_comm]
    simp_rw [sum_comm (s := range (2 ^ q))]
    have : ∀ z ∈ E, ∀ z' ∈ E,
        ∑ ξ ∈ range (2 ^ q), eC ((ξ : ℝ) * ((z' : ℤ) - z : ℤ) / (2 ^ q : ℕ)) =
          if z' = z then ((2 ^ q : ℕ) : ℂ) else 0 := by
      intro z hz z' hz'
      rw [D_sum_eC_range _ hQ]
      have hz1 := mem_range.mp (hE hz); have hz2 := mem_range.mp (hE hz')
      congr 1
      apply propext; constructor
      · intro hd
        have h1 : (z : ℤ) < ((2 ^ q : ℕ) : ℤ) := by exact_mod_cast hz1
        have h2 : (z' : ℤ) < ((2 ^ q : ℕ) : ℤ) := by exact_mod_cast hz2
        have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
        omega
      · intro h; rw [h]; simp
    rw [sum_congr rfl (fun z hz => sum_congr rfl (fun z' hz' => this z hz z' hz'))]
    simp only [sum_ite_eq']
    rw [sum_ite_mem, inter_self, sum_const]
    push_cast; ring
  exact_mod_cast h2

lemma D_W_le (q : ℕ) (E : Finset ℕ) (hE : E ⊆ range (2 ^ q)) :
    Wsum q E ≤ (2:ℝ) ^ q * E.card := by
  rw [← D_parseval q E hE, Wsum]
  exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)

lemma D_Eset_sub (q : ℕ) (y : ℝ) : Eset q y ⊆ range (2 ^ q) := by
  classical
  intro z hz; unfold Eset at hz; exact (mem_filter.mp hz).1

/-! ## Estimate of the coefficients `ω` of Lemma 5.1 -/

/-- `ω(N) = 3^{−L} Σ_{g<3^L} e(gN/(2^q 3^L))` (the `ω_ξ(η)` of Lemma 5.1 written in terms of `N`). -/
noncomputable def D_om (q L : ℕ) (N : ℤ) : ℂ :=
  (1 / (3 ^ L : ℂ)) * ∑ h ∈ range (3 ^ L), eC ((h : ℝ) * N / (2 ^ q * 3 ^ L))

lemma D_norm_om_le_one (q L : ℕ) (N : ℤ) : ‖D_om q L N‖ ≤ 1 := by
  unfold D_om
  rw [norm_mul]
  have h1 : ‖∑ h ∈ range (3 ^ L), eC ((h : ℝ) * N / (2 ^ q * 3 ^ L))‖ ≤ (3 ^ L : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    simp [D_norm_eC]
  have h2 : ‖(1 / (3 ^ L : ℂ))‖ = 1 / (3 ^ L : ℝ) := by simp
  rw [h2]
  calc 1 / (3 ^ L : ℝ) * _ ≤ 1 / (3 ^ L : ℝ) * (3 ^ L : ℝ) := by gcongr
    _ = 1 := by field_simp

/-- From Jordan's inequality: if `0 < |β| ≤ 1/2` then `|sin πβ| ≥ 2|β|`. -/
lemma D_abs_sin_ge (β : ℝ) (hβ : |β| ≤ 1 / 2) : 2 * |β| ≤ |Real.sin (Real.pi * β)| := by
  have hpi := Real.pi_pos
  rcases le_total 0 β with h | h
  · have := Real.mul_le_sin (x := Real.pi * β) (by positivity)
      (by rw [abs_of_nonneg h] at hβ; nlinarith)
    rw [abs_of_nonneg h]
    have e : 2 / Real.pi * (Real.pi * β) = 2 * β := by field_simp
    rw [e] at this
    exact this.trans (le_abs_self _)
  · have := Real.mul_le_sin (x := Real.pi * (-β)) (by nlinarith)
      (by rw [abs_of_nonpos h] at hβ; nlinarith)
    rw [abs_of_nonpos h]
    have e : 2 / Real.pi * (Real.pi * (-β)) = 2 * (-β) := by field_simp
    rw [e, show Real.pi * -β = -(Real.pi * β) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

/-- If `N ≠ 0` and `2|N| ≤ 2^q 3^L` then `‖ω(N)‖ ≤ 2^q/(2|N|)`. -/
lemma D_norm_om_le (q L : ℕ) (N : ℤ) (hN : N ≠ 0) (hN2 : 2 * |(N : ℝ)| ≤ 2 ^ q * 3 ^ L) :
    ‖D_om q L N‖ ≤ 2 ^ q / (2 * |(N : ℝ)|) := by
  set Q : ℝ := 2 ^ q with hQ
  set M : ℝ := 3 ^ L with hM
  have hQp : 0 < Q := by positivity
  have hMp : 0 < M := by positivity
  have hNa : 0 < |(N : ℝ)| := by rw [abs_pos]; exact_mod_cast hN
  set β : ℝ := N / (Q * M) with hβ
  have hβa : |β| = |(N : ℝ)| / (Q * M) := by rw [hβ, abs_div, abs_of_pos (by positivity : 0 < Q * M)]
  have hβpos : 0 < |β| := by rw [hβa]; positivity
  have hβhalf : |β| ≤ 1 / 2 := by rw [hβa, div_le_iff₀ (by positivity)]; linarith
  set r := eC β with hr
  have hpow : ∀ h : ℕ, eC ((h : ℝ) * N / (Q * M)) = r ^ h := by
    intro h; rw [hr, ← D_eC_nat_mul, hβ]; ring_nf
  have hsin := D_abs_sin_ge β hβhalf
  have hr1n : 4 * |β| ≤ ‖r - 1‖ := by rw [hr, D_norm_eC_sub_one]; linarith
  have hr1 : r ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hr1n; linarith
  unfold D_om
  rw [← hQ, ← hM]
  simp_rw [hpow]
  have hnum : ‖r ^ (3 ^ L) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hr, D_norm_eC]; norm_num
  have hden : 0 < ‖r - 1‖ := by linarith
  have h1M : ‖(1 / (3 ^ L : ℂ))‖ = 1 / M := by simp [hM]
  rw [geom_sum_eq hr1, norm_mul, h1M, norm_div]
  calc 1 / M * (‖r ^ (3 ^ L) - 1‖ / ‖r - 1‖) ≤ 1 / M * (2 / (4 * |β|)) := by
        gcongr
    _ = Q / (2 * |(N : ℝ)|) := by rw [hβa]; field_simp; ring

/-! ## Lemma 5.1: Fourier expansion on `ℤ/3^L` -/

lemma D_psi_int (M : ℕ) [NeZero M] (j : ℤ) : ZMod.stdAddChar (j : ZMod M) = eC (j / M) := by
  rw [ZMod.stdAddChar_coe]; unfold eC; push_cast; ring_nf

/-- `ω_ξ(η) = 3^{−L} Σ_{g<3^L} e(ξg/2^q) ψ(−ηg)` (Lemma 5.1). -/
noncomputable def D_omega (q L : ℕ) (ξ : ℤ) (η : ZMod (3 ^ L)) : ℂ :=
  (1 / (3 ^ L : ℂ)) * ∑ h ∈ range (3 ^ L), eC ((ξ : ℝ) * h / 2 ^ q) *
    ZMod.stdAddChar (-(η * (h : ZMod (3 ^ L))))

/-- The expansion of Lemma 5.1: if `0 ≤ g < 3^L` then `e(ξg/2^q) = Σ_η ω_ξ(η) ψ(ηg)`. -/
lemma D_expand (q L : ℕ) (ξ : ℤ) (g : ℤ) (hg0 : 0 ≤ g) (hg1 : g < 3 ^ L) :
    eC ((ξ : ℝ) * g / 2 ^ q) =
      ∑ η : ZMod (3 ^ L), D_omega q L ξ η * ZMod.stdAddChar (η * (g : ZMod (3 ^ L))) := by
  classical
  have hMp : 0 < 3 ^ L := by positivity
  unfold D_omega
  have step1 : ∀ η : ZMod (3 ^ L), ((1 / (3 ^ L : ℂ)) * ∑ h ∈ range (3 ^ L),
      eC ((ξ : ℝ) * h / 2 ^ q) * ZMod.stdAddChar (-(η * (h : ZMod (3 ^ L))))) *
        ZMod.stdAddChar (η * (g : ZMod (3 ^ L))) =
      ∑ h ∈ range (3 ^ L), (1 / (3 ^ L : ℂ)) * eC ((ξ : ℝ) * h / 2 ^ q) *
        ZMod.stdAddChar (η * ((g : ZMod (3 ^ L)) - (h : ZMod (3 ^ L)))) := by
    intro η
    rw [mul_assoc, sum_mul, mul_sum]
    apply sum_congr rfl; intro h _
    rw [mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 3; ring
  rw [sum_congr rfl (fun η _ => step1 η), sum_comm]
  simp_rw [← mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (3 ^ L)), ZMod.card]
  rw [sum_eq_single g.toNat]
  · have : (g : ZMod (3 ^ L)) - ((g.toNat : ℕ) : ZMod (3 ^ L)) = 0 := by
      rw [sub_eq_zero]
      exact_mod_cast (congrArg (fun x : ℤ => (x : ZMod (3 ^ L))) (Int.toNat_of_nonneg hg0)).symm
    rw [if_pos this]
    have e : ((g.toNat : ℕ) : ℝ) = (g : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hg0
    rw [e]
    push_cast
    field_simp
  · intro h hh hne
    have hh' := mem_range.mp hh
    have : (g : ZMod (3 ^ L)) - (h : ZMod (3 ^ L)) ≠ 0 := by
      intro e
      have e2 : ((g - h : ℤ) : ZMod (3 ^ L)) = 0 := by push_cast; exact e
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at e2
      have h1 : (h : ℤ) < ((3 ^ L : ℕ) : ℤ) := by exact_mod_cast hh'
      have h2 : g < ((3 ^ L : ℕ) : ℤ) := by exact_mod_cast hg1
      have := Int.eq_zero_of_abs_lt_dvd e2 (by rw [abs_lt]; constructor <;> omega)
      apply hne; omega
    rw [if_neg this]; simp
  · intro h; exfalso; apply h; rw [mem_range]
    have h2 : g < ((3 ^ L : ℕ) : ℤ) := by exact_mod_cast hg1
    omega

/-- If `ξ3^L − η 2^q ≡ N` (mod `2^q 3^L`) then `ω_ξ(η) = ω(N)`. -/
lemma D_omega_eq (q L : ℕ) (ξ : ℤ) (η : ZMod (3 ^ L)) (N m : ℤ)
    (h : ξ * 3 ^ L - (η.val : ℤ) * 2 ^ q = N + 2 ^ q * 3 ^ L * m) :
    D_omega q L ξ η = D_om q L N := by
  unfold D_omega D_om
  congr 1
  apply sum_congr rfl; intro g _
  have e1 : -(η * (g : ZMod (3 ^ L))) = ((-((η.val : ℤ) * g) : ℤ) : ZMod (3 ^ L)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [e1, D_psi_int, ← D_eC_add]
  have e2 : (ξ : ℝ) * g / 2 ^ q + ((-((η.val : ℤ) * g) : ℤ) : ℝ) / ((3 ^ L : ℕ) : ℝ) =
      (g : ℝ) * N / (2 ^ q * 3 ^ L) + ((g * m : ℤ) : ℝ) := by
    have h' : (ξ : ℝ) * 3 ^ L - (η.val : ℝ) * 2 ^ q = N + 2 ^ q * 3 ^ L * m := by exact_mod_cast h
    push_cast
    field_simp
    linear_combination (g : ℝ) * h'
  rw [e2, D_eC_add_int]

/-! ## Periodic sums and shells -/

lemma D_per_shift (f : ℤ → ℝ) (Q : ℕ) (hf : ∀ N, f (N + Q) = f N) (a : ℤ) :
    ∑ i ∈ range Q, f (a + i) = ∑ i ∈ range Q, f i := by
  have step : ∀ b : ℤ, ∑ i ∈ range Q, f (b + 1 + i) = ∑ i ∈ range Q, f (b + i) := by
    intro b
    have h1 := sum_range_succ' (fun i : ℕ => f (b + i)) Q
    have h2 := sum_range_succ (fun i : ℕ => f (b + i)) Q
    have e : ∀ i : ℕ, f (b + ((i + 1 : ℕ) : ℤ)) = f (b + 1 + i) := by
      intro i; congr 1; push_cast; ring
    simp only [e, Nat.cast_zero, add_zero] at h1 h2
    rw [hf b] at h2
    linarith
  induction a using Int.induction_on with
  | zero => simp
  | succ n ih => rw [step, ih]
  | pred n ih =>
    rw [← ih, ← step (-(n : ℤ) - 1)]
    congr 1; ext i; congr 1; ring

lemma D_per_Ico (f : ℤ → ℝ) (Q : ℕ) (hf : ∀ N, f (N + Q) = f N) (a : ℤ) (m : ℕ) :
    ∑ N ∈ Ico a (a + m * Q), f N = m * ∑ i ∈ range Q, f i := by
  rw [Int.Ico_eq_finset_map, sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  rw [show (a + m * Q - a).toNat = m * Q by omega]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show (m + 1) * Q = m * Q + Q by ring, sum_range_add, ih]
    have : ∑ x ∈ range Q, f (a + ((m * Q + x : ℕ) : ℤ)) = ∑ i ∈ range Q, f i := by
      rw [← D_per_shift f Q hf (a + (m * Q : ℕ))]
      apply sum_congr rfl; intro i _; congr 1; push_cast; ring
    rw [this]; push_cast; ring

/-- Shell size factor: `J_0` consists of 1 period, `J_k` (`k ≥ 1`) of `2·3^{k−1}` periods. -/
noncomputable def D_shc (k : ℕ) : ℝ := if k = 0 then 1 else 2 * 3 ^ (k - 1)

/-- Sum of a periodic function over a shell. -/
lemma D_shell_sum (q : ℕ) (hq : 1 ≤ q) (f : ℤ → ℝ) (hf : ∀ N, f (N + 2 ^ q) = f N) (k : ℕ) :
    ∑ N ∈ shell q k, f N = D_shc k * ∑ i ∈ range (2 ^ q), f i := by
  have hf' : ∀ N, f (N + ((2 ^ q : ℕ) : ℤ)) = f N := by intro N; push_cast; exact hf N
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  unfold shell D_shc
  simp only [Nat.add_sub_cancel]
  split_ifs with hk
  · have := D_per_Ico f (2 ^ (q' + 1)) hf' (-(2 ^ q' : ℤ)) 1
    rw [show -(2 ^ q' : ℤ) + ((1 : ℕ) : ℤ) * ((2 ^ (q' + 1) : ℕ) : ℤ) = 2 ^ q' by push_cast; ring] at this
    rw [this]; simp
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [sum_union]
    · have h1 := D_per_Ico f (2 ^ (q' + 1)) hf' ((2 ^ q' : ℤ) * 3 ^ k') (3 ^ k')
      have h2 := D_per_Ico f (2 ^ (q' + 1)) hf' (-((2 ^ q' : ℤ) * 3 ^ (k' + 1))) (3 ^ k')
      rw [show (2 ^ q' : ℤ) * 3 ^ k' + ((3 ^ k' : ℕ) : ℤ) * ((2 ^ (q' + 1) : ℕ) : ℤ) =
        2 ^ q' * 3 ^ (k' + 1) by push_cast; ring] at h1
      rw [show -((2 ^ q' : ℤ) * 3 ^ (k' + 1)) + ((3 ^ k' : ℕ) : ℤ) * ((2 ^ (q' + 1) : ℕ) : ℤ) =
        -(2 ^ q' * 3 ^ k') by push_cast; ring] at h2
      rw [h1, h2]; push_cast; ring
    · rw [disjoint_left]
      intro N h1 h2
      simp only [mem_Ico] at h1 h2
      have : (0 : ℤ) < 2 ^ q' * 3 ^ k' := by positivity
      linarith [h1.1, h2.2]

/-- The shells cover `[−2^{q−1}3^m, 2^{q−1}3^m)`. -/
lemma D_shell_cover (q m : ℕ) (N : ℤ) (h1 : -((2 : ℤ) ^ (q - 1) * 3 ^ m) ≤ N)
    (h2 : N < 2 ^ (q - 1) * 3 ^ m) : ∃ k ≤ m, N ∈ shell q k := by
  induction m with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    unfold shell; simp only [ite_true, mem_Ico]; simp at h1 h2; exact ⟨h1, h2⟩
  | succ m ih =>
    by_cases h : -((2 : ℤ) ^ (q - 1) * 3 ^ m) ≤ N ∧ N < 2 ^ (q - 1) * 3 ^ m
    · obtain ⟨k, hk, hN⟩ := ih h.1 h.2
      exact ⟨k, by omega, hN⟩
    · refine ⟨m + 1, le_rfl, ?_⟩
      unfold shell
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, mem_union, mem_Ico]
      rw [not_and_or, not_le, not_lt] at h
      rcases h with h | h
      · right; exact ⟨h1, h⟩
      · left; exact ⟨h, h2⟩

/-- On the shell `J_k` (`k ≥ 1`), `2^{q−1}3^{k−1} ≤ |N| ≤ 2^{q−1}3^k`. -/
lemma D_shell_abs (q k : ℕ) (hk : 1 ≤ k) (N : ℤ) (hN : N ∈ shell q k) :
    (2 : ℤ) ^ (q - 1) * 3 ^ (k - 1) ≤ |N| ∧ |N| ≤ 2 ^ (q - 1) * 3 ^ k := by
  unfold shell at hN
  rw [if_neg (by omega), mem_union, mem_Ico, mem_Ico] at hN
  have hpos : (0 : ℤ) < 2 ^ (q - 1) * 3 ^ (k - 1) := by positivity
  rcases hN with h | h
  · rw [abs_of_nonneg (by linarith)]; exact ⟨h.1, h.2.le⟩
  · rw [abs_of_neg (by linarith)]; constructor <;> linarith

/-- The upper bound `bnd_k = 3^{−(k−1)}` of `ω` on the shells (1 for `k = 0`). -/
noncomputable def D_bnd (k : ℕ) : ℝ := ((3 : ℝ) ^ (k - 1))⁻¹

lemma D_bnd_nonneg (k : ℕ) : 0 ≤ D_bnd k := by unfold D_bnd; positivity

lemma D_bnd_shc (k : ℕ) : D_bnd k * D_shc k ≤ 2 := by
  unfold D_bnd D_shc
  split_ifs with h
  · subst h; norm_num
  · field_simp; norm_num

lemma D_norm_om_shell (q L k : ℕ) (hq : 1 ≤ q) (hk : k ≤ L) (N : ℤ) (hN : N ∈ shell q k) :
    ‖D_om q L N‖ ≤ D_bnd k := by
  rcases Nat.eq_zero_or_pos k with h0 | hk1
  · subst h0; unfold D_bnd; simpa using D_norm_om_le_one q L N
  · obtain ⟨ha1, ha2⟩ := D_shell_abs q k hk1 N hN
    have ha1' : (2 : ℝ) ^ (q - 1) * 3 ^ (k - 1) ≤ |(N : ℝ)| := by exact_mod_cast ha1
    have ha2' : |(N : ℝ)| ≤ (2 : ℝ) ^ (q - 1) * 3 ^ k := by exact_mod_cast ha2
    have hpos : (0 : ℝ) < 2 ^ (q - 1) * 3 ^ (k - 1) := by positivity
    have hN0 : N ≠ 0 := by
      have : (0:ℝ) < |(N:ℝ)| := lt_of_lt_of_le hpos ha1'
      intro e; rw [e] at this; simp at this
    have hq2 : (2 : ℝ) ^ q = 2 * 2 ^ (q - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h3 : (3 : ℝ) ^ k ≤ 3 ^ L := pow_le_pow_right₀ (by norm_num) hk
    have h4 : (2 : ℝ) ^ (q - 1) * 3 ^ k ≤ 2 ^ (q - 1) * 3 ^ L :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have := D_norm_om_le q L N hN0 (by rw [hq2]; linarith)
    refine this.trans ?_
    unfold D_bnd
    rw [hq2, div_le_iff₀ (by positivity)]
    calc 2 * 2 ^ (q - 1) = ((3 : ℝ) ^ (k - 1))⁻¹ * (2 * (2 ^ (q - 1) * 3 ^ (k - 1))) := by
          field_simp
      _ ≤ ((3 : ℝ) ^ (k - 1))⁻¹ * (2 * |(N : ℝ)|) := by gcongr

end Collatz.M1
