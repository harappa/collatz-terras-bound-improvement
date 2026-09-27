import CollatzProof.M1.Fourier

/-!
# Auxiliary results: general lemmas for §8 and §9

- `G_sign_core`: the core of Lemma 8.5 (indexed by a finite set, coefficients `|c_i| ≤ 2`).
- `G_three_eq_rpow`: `3 = 2^λ`.
- (For §9) the bound on geometric series (`G_geom_bound`), the expansion of `cos²` (`G_cos_sq_eq`, `G_riesz_expand`),
  the bound on the sum of a Riesz product over an interval (`G_riesz_sum`), and the lower bound on frequencies (`G_sep`).
-/

namespace Collatz.M1

open Finset

/-- The core of Lemma 8.5 (indexed by a finite set): if the `d_i ≥ 2` are distinct and of the same parity, the `u_i` are odd, `|c_i| ≤ 2`, and
`Σ c_i u_i 2^{−d_i} ∈ ℤ`, then all `c_i = 0`. -/
theorem G_sign_core {ι : Type*} (s : Finset ι) (d : ι → ℕ) (u c : ι → ℤ)
    (hd2 : ∀ i ∈ s, 2 ≤ d i) (hinj : Set.InjOn d s) (hpar : ∀ i ∈ s, ∀ j ∈ s, d i % 2 = d j % 2)
    (hu : ∀ i ∈ s, u i % 2 = 1) (hc : ∀ i ∈ s, |c i| ≤ 2)
    (hz : ∃ z : ℤ, ∑ i ∈ s, ((c i : ℝ) * u i) / 2 ^ d i = z) : ∀ i ∈ s, c i = 0 := by
  classical
  by_contra hne
  push Not at hne
  set S := s.filter (fun i => c i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi, hci⟩ := hne
    exact ⟨i, by rw [hS, Finset.mem_filter]; exact ⟨hi, hci⟩⟩
  obtain ⟨i0, hi0S, hmax⟩ := Finset.exists_max_image S d hSne
  rw [hS, Finset.mem_filter] at hi0S
  obtain ⟨hi0, hci0⟩ := hi0S
  obtain ⟨z, hz⟩ := hz
  set D := d i0 with hD
  have hD2 : 2 ≤ D := hd2 i0 hi0
  -- the other terms become integers after multiplying by 2^{D−2}
  set t : ι → ℤ := fun i => if c i = 0 then 0 else c i * u i * 2 ^ (D - 2 - d i) with ht
  have hterm : ∀ i ∈ s.erase i0, ((c i : ℝ) * u i) / 2 ^ d i * 2 ^ (D - 2) = t i := by
    intro i hi
    rw [Finset.mem_erase] at hi
    obtain ⟨hne0, his⟩ := hi
    by_cases hci : c i = 0
    · simp [ht, hci]
    · have hle : d i ≤ D := hmax i (by rw [hS, Finset.mem_filter]; exact ⟨his, hci⟩)
      have hneq : d i ≠ D := fun h => hne0 (hinj his hi0 h)
      have hp := hpar i his i0 hi0
      have hle2 : d i + 2 ≤ D := by omega
      simp only [ht, hci, ite_false]
      push_cast
      have : (2 : ℝ) ^ (D - 2) = 2 ^ (D - 2 - d i) * 2 ^ d i := by
        rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
  have hsplit := Finset.add_sum_erase s (fun i => ((c i : ℝ) * u i) / 2 ^ d i) hi0
  have h4 : ((c i0 : ℝ) * u i0) / 2 ^ D * 2 ^ (D - 2) = (c i0 * u i0) / 4 := by
    have : (2 : ℝ) ^ D = 2 ^ (D - 2) * 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    rw [this]; field_simp
  have hsum : (c i0 * u i0 : ℝ) / 4 + ∑ i ∈ s.erase i0, (t i : ℝ) = z * 2 ^ (D - 2) := by
    rw [← h4, ← Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← add_mul, hsplit, hz]
  have hint : c i0 * u i0 = 4 * (z * 2 ^ (D - 2) - ∑ i ∈ s.erase i0, t i) := by
    have : (c i0 * u i0 : ℝ) = 4 * (z * 2 ^ (D - 2) - ∑ i ∈ s.erase i0, (t i : ℝ)) := by
      linarith
    exact_mod_cast this
  have hdvd : (4 : ℤ) ∣ c i0 * u i0 := ⟨_, hint⟩
  have hu0 := hu i0 hi0
  have hc0 := hc i0 hi0
  rw [abs_le] at hc0
  obtain ⟨w, hw⟩ := hdvd
  have : c i0 = -2 ∨ c i0 = -1 ∨ c i0 = 1 ∨ c i0 = 2 := by omega
  rcases this with h | h | h | h <;> rw [h] at hw <;> omega

/-- `3 = 2^λ`. -/
theorem G_three_eq_rpow : (3 : ℝ) = (2 : ℝ) ^ lam := by
  rw [lam, Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]

/-! ## Exponential sums and geometric series -/

/-- `e(a + b) = e(a)e(b)`. -/
theorem G_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC; push_cast; rw [← Complex.exp_add]; ring_nf

/-- `e(−a)e(a) = 1`. -/
theorem G_eC_neg (a : ℝ) : eC (-a) * eC a = 1 := by
  rw [← G_eC_add]; simp [eC]

/-- `e(xβ) = e(β)^x`. -/
theorem G_eC_nat_mul (x : ℕ) (β : ℝ) : eC (x * β) = eC β ^ x := by
  unfold eC; rw [← Complex.exp_nat_mul]; push_cast; ring_nf

/-- `|e(a)| = 1`. -/
theorem G_norm_eC (a : ℝ) : ‖eC a‖ = 1 := by
  unfold eC
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) = ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `Π e(f_i) = e(Σ f_i)`. -/
theorem G_eC_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) : ∏ i ∈ S, eC (f i) = eC (∑ i ∈ S, f i) := by
  unfold eC; rw [← Complex.exp_sum]; push_cast; rw [Finset.mul_sum]

/-- `|e(β) − 1| = |2 sin πβ|`. -/
theorem G_norm_eC_sub_one (β : ℝ) : ‖eC β - 1‖ = |2 * Real.sin (Real.pi * β)| := by
  unfold eC
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) = Complex.I * ((2 * Real.pi * β : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  congr 3; ring

/-- If `‖β‖_{ℝ/ℤ} ≥ η` then `|sin πβ| ≥ 2η` (Jordan's inequality). -/
theorem G_sin_lower (β η : ℝ) (hsep : ∀ m : ℤ, η ≤ |β - m|) : 2 * η ≤ |Real.sin (Real.pi * β)| := by
  set r := round β
  set γ := β - r with hγ
  have hγ2 : |γ| ≤ 1 / 2 := abs_sub_round β
  have hηγ : η ≤ |γ| := hsep r
  have hs : Real.sin (Real.pi * β) = (-1) ^ r * Real.sin (Real.pi * γ) := by
    rw [← Real.sin_add_int_mul_pi]; congr 1; rw [hγ]; ring
  have habs : |Real.sin (Real.pi * β)| = |Real.sin (Real.pi * γ)| := by
    rw [hs, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [habs]
  have hπ := Real.pi_pos
  rcases le_total 0 γ with h | h
  · have h1 : 2 / Real.pi * (Real.pi * γ) ≤ Real.sin (Real.pi * γ) :=
      Real.mul_le_sin (by positivity) (by rw [abs_of_nonneg h] at hγ2; nlinarith)
    have h2 : 2 / Real.pi * (Real.pi * γ) = 2 * γ := by field_simp
    rw [abs_of_nonneg h] at hηγ
    have := le_abs_self (Real.sin (Real.pi * γ))
    linarith
  · have h1 : 2 / Real.pi * (Real.pi * (-γ)) ≤ Real.sin (Real.pi * (-γ)) :=
      Real.mul_le_sin (by nlinarith) (by rw [abs_of_nonpos h] at hγ2; nlinarith)
    have h2 : 2 / Real.pi * (Real.pi * (-γ)) = 2 * (-γ) := by field_simp
    rw [abs_of_nonpos h] at hηγ
    have h3 : Real.sin (Real.pi * (-γ)) = - Real.sin (Real.pi * γ) := by
      rw [mul_neg, Real.sin_neg]
    have := neg_abs_le (Real.sin (Real.pi * γ))
    linarith

/-- Geometric series: if `‖β‖_{ℝ/ℤ} ≥ η > 0` then `|Σ_{x<U} e(xβ)| ≤ 1/(2η)`. -/
theorem G_geom_bound (β η : ℝ) (hη : 0 < η) (hsep : ∀ m : ℤ, η ≤ |β - m|) (U : ℕ) :
    ‖∑ x ∈ range U, eC (x * β)‖ ≤ 1 / (2 * η) := by
  simp_rw [G_eC_nat_mul]
  have hlow : 4 * η ≤ ‖eC β - 1‖ := by
    rw [G_norm_eC_sub_one, abs_mul, abs_two]
    have := G_sin_lower β η hsep
    linarith
  have hne : eC β ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hlow; linarith
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖eC β ^ U - 1‖ ≤ 2 := by
    calc ‖eC β ^ U - 1‖ ≤ ‖eC β ^ U‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, G_norm_eC, one_pow, norm_one]; norm_num
  have hpos : 0 < ‖eC β - 1‖ := by linarith
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-- `cos² πy = (1 + e(y))(1 + e(−y))/4`. -/
theorem G_cos_sq_eq (y : ℝ) :
    ((Real.cos (Real.pi * y) ^ 2 : ℝ) : ℂ) = (1 + eC y) * (1 + eC (-y)) / 4 := by
  have h1 : (1 + eC y) * (1 + eC (-y)) = 2 + (eC y + eC (-y)) := by
    have := G_eC_neg y
    linear_combination this
  have h2 : eC y + eC (-y) = 2 * ((Real.cos (2 * (Real.pi * y)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.two_cos]
    unfold eC; push_cast; ring_nf
  rw [h1, h2, Real.cos_two_mul]; push_cast; ring


/-- Expansion of the Riesz product at a single `x`: `Π_b cos² π(φ_b + xα_b) = 4^{−m} Σ_{S,S'} e(φ_S − φ_{S'}) e(x(α_S − α_{S'}))`. -/
theorem G_riesz_expand {ι : Type*} (B : Finset ι) (φ α : ι → ℝ) (x : ℝ) :
    ((∏ b ∈ B, Real.cos (Real.pi * (φ b + x * α b)) ^ 2 : ℝ) : ℂ) =
      (1 / 4) ^ B.card * ∑ S ∈ B.powerset, ∑ S' ∈ B.powerset,
        eC (∑ b ∈ S, φ b - ∑ b ∈ S', φ b) * eC (x * (∑ b ∈ S, α b - ∑ b ∈ S', α b)) := by
  rw [Complex.ofReal_prod]
  simp_rw [G_cos_sq_eq]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_one_add,
    Finset.prod_one_add, Finset.sum_mul_sum, div_eq_mul_inv, mul_comm, one_div, inv_pow]
  congr 1
  apply Finset.sum_congr rfl; intro S _
  apply Finset.sum_congr rfl; intro S' _
  rw [G_eC_sum, G_eC_sum, ← G_eC_add, ← G_eC_add]
  congr 1
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-- The sum of a Riesz product over an interval (steps 2–4 of Lemma 9.1 in §9): if for every pair of subsets `S ≠ S'`
`α_S − α_{S'}` is at distance at least `η` from the integers, then `Σ_{x<U} Π_b cos² π(φ_b + xα_b) ≤ U 2^{−|B|} + 1/(2η)`. -/
theorem G_riesz_sum {ι : Type*} [DecidableEq ι] (B : Finset ι) (φ α : ι → ℝ) (U : ℕ) (η : ℝ)
    (hη : 0 < η)
    (hsep : ∀ S ⊆ B, ∀ S' ⊆ B, S ≠ S' → ∀ m : ℤ, η ≤ |∑ b ∈ S, α b - ∑ b ∈ S', α b - m|) :
    ∑ x ∈ range U, ∏ b ∈ B, Real.cos (Real.pi * (φ b + x * α b)) ^ 2 ≤
      U * (1 / 2) ^ B.card + 1 / (2 * η) := by
  have hC : (((∑ x ∈ range U, ∏ b ∈ B, Real.cos (Real.pi * (φ b + x * α b)) ^ 2 : ℝ)) : ℂ) =
      (1 / 4) ^ B.card * ∑ S ∈ B.powerset, ∑ S' ∈ B.powerset,
        eC (∑ b ∈ S, φ b - ∑ b ∈ S', φ b) *
          ∑ x ∈ range U, eC (x * (∑ b ∈ S, α b - ∑ b ∈ S', α b)) := by
    rw [Complex.ofReal_sum]
    simp_rw [G_riesz_expand]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S' _
    rw [Finset.mul_sum]
  -- bound on each term
  have hterm : ∀ S ∈ B.powerset, ∀ S' ∈ B.powerset,
      ‖eC (∑ b ∈ S, φ b - ∑ b ∈ S', φ b) *
        ∑ x ∈ range U, eC (x * (∑ b ∈ S, α b - ∑ b ∈ S', α b))‖ ≤
        (if S = S' then (U : ℝ) else 0) + 1 / (2 * η) := by
    intro S hS S' hS'
    rw [norm_mul, G_norm_eC, one_mul]
    by_cases hSS : S = S'
    · subst hSS
      have h1 : ∀ x ∈ range U, eC ((x : ℝ) * (∑ b ∈ S, α b - ∑ b ∈ S, α b)) = 1 := fun x _ => by
        simp [eC]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, if_pos rfl]
      simp only [nsmul_eq_mul, mul_one, Complex.norm_natCast]
      have : 0 < 1 / (2 * η) := by positivity
      linarith
    · rw [if_neg hSS, zero_add]
      exact G_geom_bound _ η hη (hsep S (Finset.mem_powerset.mp hS) S' (Finset.mem_powerset.mp hS') hSS) U
  have hLHS0 : 0 ≤ ∑ x ∈ range U, ∏ b ∈ B, Real.cos (Real.pi * (φ b + x * α b)) ^ 2 := by
    apply Finset.sum_nonneg; intro x _
    apply Finset.prod_nonneg; intro b _; positivity
  have hsum_ite : ∑ S ∈ B.powerset, ∑ S' ∈ B.powerset, (if S = S' then (U : ℝ) else 0) =
      2 ^ B.card * U := by
    rw [Finset.sum_congr rfl (fun S hS => Finset.sum_ite_eq B.powerset S (fun _ => (U : ℝ)))]
    rw [Finset.sum_congr rfl (fun S hS => if_pos hS), Finset.sum_const, Finset.card_powerset,
      nsmul_eq_mul]
    push_cast; ring
  calc ∑ x ∈ range U, ∏ b ∈ B, Real.cos (Real.pi * (φ b + x * α b)) ^ 2
      = ‖(((∑ x ∈ range U, ∏ b ∈ B, Real.cos (Real.pi * (φ b + x * α b)) ^ 2 : ℝ)) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLHS0]
    _ ≤ (1 / 4) ^ B.card * ∑ S ∈ B.powerset, ∑ S' ∈ B.powerset,
          ((if S = S' then (U : ℝ) else 0) + 1 / (2 * η)) := by
      rw [hC, norm_mul, norm_pow, norm_div, norm_one, Complex.norm_ofNat]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ ∑ S ∈ B.powerset, ‖∑ S' ∈ B.powerset, eC (∑ b ∈ S, φ b - ∑ b ∈ S', φ b) *
            ∑ x ∈ range U, eC (x * (∑ b ∈ S, α b - ∑ b ∈ S', α b))‖ := norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum; intro S hS
          calc _ ≤ _ := norm_sum_le _ _
            _ ≤ _ := Finset.sum_le_sum (fun S' hS' => hterm S hS S' hS')
    _ = U * (1 / 2) ^ B.card + 1 / (2 * η) := by
      simp only [Finset.sum_add_distrib]
      rw [hsum_ite]
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
      have h4 : (1 / 4 : ℝ) ^ B.card = (1 / 2) ^ B.card * (1 / 2) ^ B.card := by
        rw [← mul_pow]; norm_num
      have h2 : (1 / 2 : ℝ) ^ B.card * 2 ^ B.card = 1 := by
        rw [← mul_pow]; norm_num
      rw [h4]; push_cast
      linear_combination (U * (1 / 2) ^ B.card + (1 / 2) ^ B.card * 2 ^ B.card * (1 / (2 * η)) +
        1 / (2 * η)) * h2

/-! ## Lower bound on frequencies -/

/-- Lower bound on frequencies (step 3 of Lemma 9.1 in §9): if `α_b = 1 + ε_b − v_b/2^{d_b}` (the `d_b ≥ 2` distinct and of the same parity, `d_b ≤ D`,
`v_b` odd, `Σ|ε_b| ≤ 2^{−D−1}`), then for every pair of subsets `S ≠ S'`, `α_S − α_{S'}` is at distance at least `2^{−D−1}` from the integers. -/
theorem G_sep {ι : Type*} [DecidableEq ι] (B : Finset ι) (d : ι → ℕ) (v : ι → ℤ) (ε : ι → ℝ) (D : ℕ)
    (hd2 : ∀ b ∈ B, 2 ≤ d b) (hdD : ∀ b ∈ B, d b ≤ D) (hinj : Set.InjOn d B)
    (hpar : ∀ i ∈ B, ∀ j ∈ B, d i % 2 = d j % 2) (hv : ∀ b ∈ B, v b % 2 = 1)
    (hε : ∑ b ∈ B, |ε b| ≤ (1 / 2) ^ (D + 1)) :
    ∀ S ⊆ B, ∀ S' ⊆ B, S ≠ S' → ∀ m : ℤ,
      (1 / 2 : ℝ) ^ (D + 1) ≤
        |∑ b ∈ S, (1 + ε b - v b / 2 ^ d b) - ∑ b ∈ S', (1 + ε b - v b / 2 ^ d b) - m| := by
  intro S hS S' hS' hne m
  set c : ι → ℤ := fun b => (if b ∈ S then 1 else 0) - (if b ∈ S' then 1 else 0) with hc
  set g : ι → ℝ := fun b => 1 + ε b - v b / 2 ^ d b with hg
  have hsum_c : ∑ b ∈ S, g b - ∑ b ∈ S', g b = ∑ b ∈ B, (c b : ℝ) * g b := by
    have e1 : ∑ b ∈ S, g b = ∑ b ∈ B, (if b ∈ S then g b else 0) := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS]
    have e2 : ∑ b ∈ S', g b = ∑ b ∈ B, (if b ∈ S' then g b else 0) := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS']
    rw [e1, e2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _
    simp only [hc]; split_ifs <;> push_cast <;> ring
  have hcabs : ∀ b, |(c b : ℝ)| ≤ 1 := by
    intro b; simp only [hc]; split_ifs <;> norm_num
  -- decomposition
  set C : ℤ := ∑ b ∈ B, c b
  set E : ℝ := ∑ b ∈ B, (c b : ℝ) * ε b
  set X : ℝ := ∑ b ∈ B, ((c b : ℝ) * v b) / 2 ^ d b
  have hdecomp : ∑ b ∈ B, (c b : ℝ) * g b = C + E - X := by
    simp only [C, E, X, hg]; push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _; ring
  have hE : |E| ≤ (1 / 2) ^ (D + 1) := by
    calc |E| ≤ ∑ b ∈ B, |(c b : ℝ) * ε b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ B, |ε b| := by
          apply Finset.sum_le_sum; intro b _
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hcabs b)
      _ ≤ _ := hε
  -- `X` is at distance at least `2^{−D}` from the integers
  have hX : ∀ m' : ℤ, (1 / 2 : ℝ) ^ D ≤ |X - m'| := by
    intro m'
    set K : ℤ := ∑ b ∈ B, c b * v b * 2 ^ (D - d b)
    have hK : (K : ℝ) = 2 ^ D * X := by
      simp only [K, X]; push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b hb
      have : (2 : ℝ) ^ D = 2 ^ (D - d b) * 2 ^ d b := by
        rw [← pow_add]; congr 1; have := hdD b hb; omega
      rw [this]; field_simp
    have hKne : K - 2 ^ D * m' ≠ 0 := by
      intro h0
      have hXm : X = m' := by
        have : (K : ℝ) = 2 ^ D * m' := by
          have : K = 2 ^ D * m' := by linarith
          exact_mod_cast this
        rw [hK] at this
        have h2 : (2 : ℝ) ^ D ≠ 0 := by positivity
        exact mul_left_cancel₀ h2 this
      have hall := G_sign_core B d v c hd2 hinj hpar hv
        (fun b _ => by have := hcabs b; exact_mod_cast (show |(c b : ℝ)| ≤ 2 by linarith))
        ⟨m', hXm⟩
      apply hne
      ext x
      constructor
      · intro hx
        have := hall x (hS hx)
        simp only [hc, hx, ite_true] at this
        by_contra hx'
        simp [hx'] at this
      · intro hx
        have := hall x (hS' hx)
        simp only [hc, hx, ite_true] at this
        by_contra hx'
        simp [hx'] at this
    have h1 : (1 : ℝ) ≤ |(K : ℝ) - 2 ^ D * m'| := by
      have := Int.one_le_abs hKne
      exact_mod_cast this
    have hXeq : X - m' = ((K : ℝ) - 2 ^ D * m') / 2 ^ D := by
      rw [hK]; field_simp
    rw [hXeq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ D), div_pow, one_pow]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  rw [hsum_c, hdecomp]
  have hXC := hX (C - m)
  have htri : |X - ((C - m : ℤ) : ℝ)| ≤ |(C : ℝ) + E - X - m| + |E| := by
    have : X - ((C - m : ℤ) : ℝ) = -((C : ℝ) + E - X - m) + E := by push_cast; ring
    rw [this]
    calc |-((C : ℝ) + E - X - m) + E| ≤ |-((C : ℝ) + E - X - m)| + |E| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hpow : (1 / 2 : ℝ) ^ D = 2 * (1 / 2) ^ (D + 1) := by rw [pow_succ]; ring
  linarith

end Collatz.M1
