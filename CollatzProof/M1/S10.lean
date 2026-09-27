import CollatzProof.M1.Phase

/-!
# §10: Hölder reduction for shell 0 and the inner shells

Proof of Proposition 10.2 of the manuscript (§10; Proposition 12.2 of the paper). Auxiliary declarations have the prefix `H_`. Correspondence with the steps of the manuscript:
- Steps 1–4 (dropping the part outside the window, phase, expansion, error): the pointwise estimate `H_pointwise` for each tail `τ` and each `N ∈ J_k`
  (the error is `H_err_le`). The elements of the window `B' = {b ∈ ℬ(τ) | d_b ≤ D}` are numbered by `H_b : Fin #B' → ℕ`.
- Step 5 (range of `β`): `H_beta_mem` (Lemma 8.4).
- Steps 6, 7 (shell 0 and the inner shells, the deep version of (∗) in §9): `H_fiber`, which moves the sum over the shell to a sum over `(ξ, κ)` and turns it into an average over `μ`.
- Step 8 (Hölder and injectivity): `H_holder`, `H_h_injOn`, `H_h_ne_zero` (Lemma 8.5).
- Step 9: the Lean `AkDeep` has the form of an average over tails (`ShellDefs.lean`), so it suffices to average the per-tail estimate `H_tail`.
-/

namespace Collatz.M1

open Finset

/-! ## Basic properties of `e(x) = e^{2πix}` -/

theorem H_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem H_eC_int (n : ℤ) : eC (n : ℝ) = 1 := by
  unfold eC
  have : (2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem H_eC_add_int (x : ℝ) (n : ℤ) : eC (x + n) = eC x := by
  rw [H_eC_add, H_eC_int, mul_one]

theorem H_eC_zero : eC 0 = 1 := by simpa using H_eC_int 0

theorem H_norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem H_norm_eC_sub_one (x : ℝ) : ‖eC x - 1‖ ≤ 2 * Real.pi * |x| := by
  unfold eC
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by
    push_cast; ring
  rw [this]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]; norm_num

theorem H_eC_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : eC (∑ i ∈ s, f i) = ∏ i ∈ s, eC (f i) := by
  unfold eC; rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum]

/-! ## Expansion of `cos²` and the weights `P(σ)` (§8.3) -/

/-- Weights `P(0) = 1/2`, `P(±1) = 1/4`. -/
noncomputable def H_Pw (j : ℤ) : ℝ := if j = 0 then 1 / 2 else 1 / 4

/-- `{−1, 0, 1}`. -/
def H_S3 : Finset ℤ := {-1, 0, 1}

/-- `cos² πy = Σ_{σ∈{−1,0,1}} P(σ) e(σy)`. -/
theorem H_cos_sq (y : ℝ) :
    ((Real.cos (Real.pi * y) ^ 2 : ℝ) : ℂ) = ∑ j ∈ H_S3, (H_Pw j : ℂ) * eC (j * y) := by
  simp only [H_S3, H_Pw]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
  unfold eC
  push_cast
  rw [Complex.cos_sq, Complex.cos]
  have h1 : 2 * ((Real.pi : ℂ) * y) * Complex.I = 2 * Real.pi * Complex.I * y := by ring
  have h2 : -(2 * ((Real.pi : ℂ) * y)) * Complex.I = 2 * Real.pi * Complex.I * (-y) := by ring
  rw [h1, h2]; ring_nf; rw [Complex.exp_zero]; ring

theorem H_sum_Pw : ∑ j ∈ H_S3, H_Pw j = 1 := by
  simp only [H_S3, H_Pw]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- `P(σ) = Π_b P(σ_b)`. -/
noncomputable def H_Pσ {n : ℕ} (σ : Fin n → ℤ) : ℝ := ∏ i, H_Pw (σ i)

theorem H_Pw_nonneg (j : ℤ) : 0 ≤ H_Pw j := by unfold H_Pw; split_ifs <;> norm_num

theorem H_Pσ_nonneg {n : ℕ} (σ : Fin n → ℤ) : 0 ≤ H_Pσ σ :=
  Finset.prod_nonneg (fun _ _ => H_Pw_nonneg _)

/-- `Π_b cos² πy_b = Σ_σ P(σ) e(Σ_b σ_b y_b)` (§8.3). -/
theorem H_prod_cos_sq {n : ℕ} (y : Fin n → ℝ) :
    ((∏ i, Real.cos (Real.pi * y i) ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => H_S3), (H_Pσ σ : ℂ) * eC (∑ i, (σ i : ℝ) * y i) := by
  rw [Complex.ofReal_prod]
  simp_rw [H_cos_sq]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_mul_distrib, H_eC_sum, H_Pσ]; push_cast; rfl

/-- `Σ_σ P(σ) = 1`. -/
theorem H_sum_Pσ (n : ℕ) : ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => H_S3), H_Pσ σ = 1 := by
  unfold H_Pσ
  rw [← Finset.prod_univ_sum (fun _ : Fin n => H_S3) (fun _ j => H_Pw j)]
  simp [H_sum_Pw]

/-- `Σ_σ P(σ)^r = (Σ_j P(j)^r)^n`. -/
theorem H_sum_Pσ_rpow (n : ℕ) (r : ℝ) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => H_S3), H_Pσ σ ^ r = (∑ j ∈ H_S3, H_Pw j ^ r) ^ n := by
  unfold H_Pσ
  have : ∀ σ : Fin n → ℤ, (∏ i, H_Pw (σ i)) ^ r = ∏ i, H_Pw (σ i) ^ r := by
    -- `Real.finsetProd_rpow` (v4.34) is `Real.finset_prod_rpow` in v4.30. We use the latter, which exists in both versions (a deprecation warning in v4.34)
    intro σ; rw [Real.finset_prod_rpow]; intro _ _; exact H_Pw_nonneg _
  simp_rw [this]
  rw [← Finset.prod_univ_sum (fun _ : Fin n => H_S3) (fun _ j => H_Pw j ^ r)]
  simp

theorem H_Pσ_zero (n : ℕ) : H_Pσ (0 : Fin n → ℤ) = (1 / 2) ^ n := by
  simp [H_Pσ, H_Pw]

theorem H_zero_mem (n : ℕ) : (0 : Fin n → ℤ) ∈ Fintype.piFinset (fun _ : Fin n => H_S3) := by
  simp [Fintype.mem_piFinset, H_S3]

theorem H_abs_le_one {n : ℕ} {σ : Fin n → ℤ} (hσ : σ ∈ Fintype.piFinset (fun _ : Fin n => H_S3))
    (i : Fin n) : |σ i| ≤ 1 := by
  rw [Fintype.mem_piFinset] at hσ
  have := hσ i
  simp only [H_S3, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h <;> rw [h] <;> norm_num

/-- `Σ_j P(j)^{p'} = 2^{−p'} + 2^{1−2p'}`. -/
theorem H_sum_Pw_rpow (r : ℝ) : ∑ j ∈ H_S3, H_Pw j ^ r = (2:ℝ) ^ (-r) + (2:ℝ) ^ (1 - 2 * r) := by
  simp only [H_S3, H_Pw]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
  have h4 : (4:ℝ)⁻¹ ^ r = (2:ℝ) ^ (-2 * r) := by
    rw [show (4:ℝ)⁻¹ = (2:ℝ) ^ (-2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  have h2 : (2:ℝ)⁻¹ ^ r = (2:ℝ) ^ (-r) := by
    rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  rw [one_div, one_div, h4, h2, show (1:ℝ) - 2 * r = 1 + (-2 * r) by ring, Real.rpow_add (by norm_num)]
  ring

/-! ## The index `h_σ` of a sign sequence (end of §8.3, Lemma 8.5) -/

section Code
variable {n : ℕ} (D : ℕ) (d : Fin n → ℕ) (u : Fin n → ℤ)

/-- `z_σ = Σ_b σ_b u_b 2^{D − d_b}` (`X_σ = z_σ/2^D`). -/
def H_z (σ : Fin n → ℤ) : ℤ := ∑ i, σ i * u i * 2 ^ (D - d i)

/-- `h_σ = z_σ mod 2^D ∈ [0, 2^D)`. -/
def H_h (σ : Fin n → ℤ) : ℕ := (H_z D d u σ % 2 ^ D).toNat

theorem H_h_cast (σ : Fin n → ℤ) : (H_h D d u σ : ℤ) = H_z D d u σ % 2 ^ D := by
  unfold H_h; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]

theorem H_h_lt (σ : Fin n → ℤ) : H_h D d u σ < 2 ^ D := by
  have h1 := H_h_cast D d u σ
  have h2 : H_z D d u σ % 2 ^ D < 2 ^ D := Int.emod_lt_of_pos _ (by positivity)
  have : ((H_h D d u σ : ℕ) : ℤ) < ((2 ^ D : ℕ) : ℤ) := by push_cast; omega
  exact_mod_cast this

theorem H_z_real (hdD : ∀ i, d i ≤ D) (σ : Fin n → ℤ) :
    (H_z D d u σ : ℝ) / 2 ^ D = ∑ i, (σ i : ℝ) * u i / 2 ^ d i := by
  unfold H_z; push_cast; rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : (2:ℝ) ^ D = 2 ^ (D - d i) * 2 ^ d i := by rw [← pow_add, Nat.sub_add_cancel (hdD i)]
  rw [this]; field_simp

theorem H_z_split (σ : Fin n → ℤ) :
    (H_z D d u σ : ℝ) = H_h D d u σ + 2 ^ D * ((H_z D d u σ / 2 ^ D : ℤ) : ℝ) := by
  have h := Int.emod_add_mul_ediv (H_z D d u σ) (2 ^ D)
  have h1 := H_h_cast D d u σ
  have : (H_z D d u σ : ℤ) = (H_h D d u σ : ℤ) + 2 ^ D * (H_z D d u σ / 2 ^ D) := by omega
  exact_mod_cast this

/-- `κ X_σ ≡ h_σ κ/2^D (mod 1)` (`X_σ = Σ_b σ_b u_b 2^{−d_b}`). -/
theorem H_X_int (hdD : ∀ i, d i ≤ D) (σ : Fin n → ℤ) (κ : ℤ) :
    ∃ m : ℤ, (κ : ℝ) * ∑ i, (σ i : ℝ) * u i / 2 ^ d i = (H_h D d u σ : ℝ) * κ / 2 ^ D + m := by
  refine ⟨κ * (H_z D d u σ / 2 ^ D), ?_⟩
  rw [← H_z_real D d u hdD, H_z_split D d u σ]
  push_cast; field_simp

theorem H_h_zero : H_h D d u (0 : Fin n → ℤ) = 0 := by simp [H_h, H_z]

variable (hd2 : ∀ i, 2 ≤ d i) (hinj : Function.Injective d) (hpar : ∀ i j, d i % 2 = d j % 2)
  (hu : ∀ i, u i % 2 = 1) (hdD : ∀ i, d i ≤ D)
include hd2 hinj hpar hu hdD

/-- Lemma 8.5: `σ ↦ h_σ` is injective on `{−1,0,1}^n`. -/
theorem H_h_injOn : Set.InjOn (H_h D d u) (Fintype.piFinset (fun _ : Fin n => H_S3) : Set _) := by
  intro σ hσ σ' hσ' heq
  have hσ1 := fun i => H_abs_le_one (Finset.mem_coe.1 hσ) i
  have hσ1' := fun i => H_abs_le_one (Finset.mem_coe.1 hσ') i
  refine sign_inj d u hd2 hinj hpar hu σ σ' hσ1 hσ1' ⟨H_z D d u σ / 2 ^ D - H_z D d u σ' / 2 ^ D, ?_⟩
  have e1 := H_z_real D d u hdD σ
  have e2 := H_z_real D d u hdD σ'
  have s1 := H_z_split D d u σ
  have s2 := H_z_split D d u σ'
  rw [heq] at s1
  have : ∑ i, (((σ i : ℝ) - σ' i) * u i) / 2 ^ d i =
      (H_z D d u σ : ℝ) / 2 ^ D - (H_z D d u σ' : ℝ) / 2 ^ D := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [this, s1, s2]; push_cast; field_simp; ring

/-- Lemma 8.5: if `σ ≠ 0` then `h_σ ≠ 0`. -/
theorem H_h_ne_zero (σ : Fin n → ℤ) (hσ : σ ∈ Fintype.piFinset (fun _ : Fin n => H_S3))
    (h0 : σ ≠ 0) : H_h D d u σ ≠ 0 := by
  intro h
  apply h0
  refine H_h_injOn D d u hd2 hinj hpar hu hdD (Finset.mem_coe.2 hσ) (Finset.mem_coe.2 (H_zero_mem n)) ?_
  rw [h, H_h_zero]

end Code

/-! ## Hölder and injectivity (step 8) -/

/-- `(Σ_σ P(σ)^{p'})^{1/p'} = φ_p^n`. -/
theorem H_phiP_pow (p : ℝ) (n : ℕ) :
    (((2:ℝ) ^ (-(p / (p - 1))) + (2:ℝ) ^ (1 - 2 * (p / (p - 1)))) ^ n) ^ (1 / (p / (p - 1))) =
      phiP p ^ n := by
  unfold phiP
  rw [Real.rpow_pow_comm (by positivity)]

/-- Step 8: by Hölder (exponents `p'`, `p`) and the injectivity of `σ ↦ h_σ ∈ [1, 2^D)`,
`Σ_{σ≠0} P(σ) T_σ ≤ φ_p^n (Σ_{h=1}^{2^D−1} Φ(h))^{1/p}` (given `T_σ^p ≤ Φ(h_σ)`). -/
theorem H_holder {n : ℕ} (p : ℝ) (hp : 1 < p) (D : ℕ) (h : (Fin n → ℤ) → ℕ)
    (hinj : Set.InjOn h ((Fintype.piFinset (fun _ : Fin n => H_S3)).erase 0 : Set _))
    (hrange : ∀ σ ∈ (Fintype.piFinset (fun _ : Fin n => H_S3)).erase 0, h σ ∈ Ico 1 (2 ^ D))
    (T : (Fin n → ℤ) → ℝ) (hT0 : ∀ σ, 0 ≤ T σ) (Φ : ℕ → ℝ) (hΦ : ∀ k, 0 ≤ Φ k)
    (hTΦ : ∀ σ ∈ (Fintype.piFinset (fun _ : Fin n => H_S3)).erase 0, T σ ^ p ≤ Φ (h σ)) :
    ∑ σ ∈ (Fintype.piFinset (fun _ : Fin n => H_S3)).erase 0, H_Pσ σ * T σ ≤
      phiP p ^ n * (∑ k ∈ Ico 1 (2 ^ D), Φ k) ^ (1 / p) := by
  set S := (Fintype.piFinset (fun _ : Fin n => H_S3)).erase 0
  have hpq : (p / (p - 1)).HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  have hp' : 0 < p / (p - 1) := hpq.pos
  refine (Real.inner_le_Lp_mul_Lq_of_nonneg S hpq (fun σ _ => H_Pσ_nonneg σ)
    (fun σ _ => hT0 σ)).trans ?_
  apply mul_le_mul
  · rw [← H_phiP_pow p n, ← H_sum_Pw_rpow, ← H_sum_Pσ_rpow]
    apply Real.rpow_le_rpow (Finset.sum_nonneg (fun σ _ => Real.rpow_nonneg (H_Pσ_nonneg σ) _))
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun σ _ _ => Real.rpow_nonneg (H_Pσ_nonneg σ) _)
    · positivity
  · apply Real.rpow_le_rpow (Finset.sum_nonneg (fun σ _ => Real.rpow_nonneg (hT0 σ) _))
    · calc ∑ σ ∈ S, T σ ^ p ≤ ∑ σ ∈ S, Φ (h σ) := Finset.sum_le_sum hTΦ
        _ = ∑ k ∈ S.image h, Φ k := (Finset.sum_image hinj).symm
        _ ≤ ∑ k ∈ Ico 1 (2 ^ D), Φ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hk; exact hrange σ hσ
          · intro k _ _; exact hΦ k
    · have : 0 < p := by linarith
      positivity
  · exact Real.rpow_nonneg (Finset.sum_nonneg (fun σ _ => Real.rpow_nonneg (hT0 σ) _)) _
  · unfold phiP; positivity

/-! ## Properties of the swap blocks (Lemma 5.3 (i) and the end of §8.3) -/

theorem H_mem_Bset {q s P : ℕ} {τ : Fin (s - P) → Bool} {b : ℕ} (hb : b ∈ Bset q s P τ) :
    IsSwap q s P τ b := by
  classical
  unfold Bset at hb; exact (Finset.mem_filter.1 hb).2

theorem H_swap_pos {q s P : ℕ} {τ : Fin (s - P) → Bool} {b : ℕ} (hb : IsSwap q s P τ b) :
    1 ≤ b ∧ 2 * b < s - P := by
  obtain ⟨h, h1, _⟩ := hb; exact ⟨h1, h⟩

/-- For a swap block, `d_b ≥ 2` (`ℓ_b ≤ t − 2`). -/
theorem H_db_ge {q s P : ℕ} {τ : Fin (s - P) → Bool} {b : ℕ} (hb : IsSwap q s P τ b) :
    2 ≤ db s P b := by
  have := H_swap_pos hb; unfold db; omega

/-- The 1 of a swap block is the `j_b`-th 1 of the tail, so `o_{2k−1}(τ) + 1 ≤ o_t(τ)`. -/
theorem H_ones_lt {q s P : ℕ} {τ : Fin (s - P) → Bool} {b : ℕ} (hb : IsSwap q s P τ b) :
    ones τ (2 * b - 1) + 1 ≤ ones τ (s - P) := by
  obtain ⟨h, h1, hne, _⟩ := hb
  unfold ones
  have hex : ∃ i0 : Fin (s - P), 2 * b - 1 ≤ (i0 : ℕ) ∧ τ i0 = true := by
    by_cases ht : τ ⟨2 * b - 1, by omega⟩ = true
    · exact ⟨_, le_refl _, ht⟩
    · refine ⟨⟨2 * b, h⟩, by simp, ?_⟩
      cases h2 : τ ⟨2 * b, h⟩
      · exfalso; apply hne; simp only [Bool.not_eq_true] at ht; rw [ht, h2]
      · rfl
  obtain ⟨i0, hi0, hi0t⟩ := hex
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i0, ?_, ?_⟩
    · simp [hi0t]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]; intro h'; omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨i.2, hi.2⟩

/-- For a swap block of `τ ∈ 𝒯`, `n_b ≤ L` (`o_t(τ) = L − L_p`). -/
theorem H_nb_le {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) {b : ℕ}
    (hb : IsSwap q s P τ b) : nb q s P τ b ≤ L := by
  classical
  have h1 := H_ones_lt hb
  unfold Tset at hτ
  have h2 := (Finset.mem_filter.1 hτ).2.2.1
  unfold nb jb; omega

/-- `n_b ≥ L_p + 1`. -/
theorem H_nb_ge {q s P : ℕ} (τ : Fin (s - P) → Bool) (b : ℕ) : Lp q + 1 ≤ nb q s P τ b := by
  unfold nb jb; omega

/-- `u_b = −3^{−n} mod 2^d` is odd (`d ≥ 1`). -/
theorem H_ub_odd (d n : ℕ) (hd : 1 ≤ d) : ((ub d n : ℕ) : ℤ) % 2 = 1 := by
  have hcop : Nat.Coprime 3 (2 ^ d) := Nat.Coprime.pow_right _ (by norm_num)
  have hu3 : IsUnit (3 : ZMod (2 ^ d)) := by
    have := (ZMod.unitOfCoprime 3 hcop).isUnit
    simpa using this
  have hmul : (3 : ZMod (2 ^ d)) ^ n * ((3 : ZMod (2 ^ d)) ^ n)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (hu3.pow n)
  have hdvd : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
  obtain ⟨y, hy⟩ : ∃ y : ZMod (2 ^ d), y = -(((3 : ZMod (2 ^ d)) ^ n)⁻¹) := ⟨_, rfl⟩
  have hy3 : y * (3 : ZMod (2 ^ d)) ^ n = -1 := by rw [hy, neg_mul, mul_comm, hmul]
  have hφ := congrArg (ZMod.castHom hdvd (ZMod 2)) hy3
  simp only [map_mul, map_pow, map_neg, map_one] at hφ
  have h3 : (ZMod.castHom hdvd (ZMod 2)) (3 : ZMod (2 ^ d)) = 1 := by
    rw [show (3 : ZMod (2 ^ d)) = ((3 : ℕ) : ZMod (2 ^ d)) by norm_num, map_natCast]; decide
  rw [h3, one_pow, mul_one] at hφ
  have hval : ((y.val : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hφ; rw [hφ]; decide
  have : y.val % 2 = 1 := by
    have := congrArg ZMod.val hval
    rwa [ZMod.val_natCast, ZMod.val_one] at this
  unfold ub; rw [← hy]; omega

/-- `2^q < 3^{L_p+1}` (maximality of `L_p`). -/
theorem H_Lp_lt (q : ℕ) : 2 ^ q < 3 ^ (Lp q + 1) := by
  have hle : Lp q ≤ q := Nat.findGreatest_le q
  by_cases h : Lp q + 1 ≤ q
  · have := Nat.findGreatest_is_greatest (P := fun l => 3 ^ l ≤ 2 ^ q) (Nat.lt_succ_self _) h
    unfold Lp; exact not_le.1 this
  · have hq : Lp q = q := by omega
    rw [hq]
    calc 2 ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by norm_num) q
      _ < 3 ^ (q + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## Fiber representation of the shell average (deep version of (∗) in §9, steps 6, 7) -/

/-- `C_k(g) = Σ_{x ∈ I_k(0)} e(g x/2^D)` (independent of `ξ`). -/
noncomputable def H_C (q L k D g : ℕ) : ℂ := ∑ x ∈ Ik q L k 0, eC ((g : ℝ) * (x : ℝ) / 2 ^ D)

/-- `κ₀(0) = 0`. -/
theorem H_kappa0_zero (q L : ℕ) (hq : 1 ≤ q) : kappa0 q L 0 = 0 := by
  unfold kappa0
  have : 2 ^ (q - 1) < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp [Nat.div_eq_of_lt this]

/-- `I_k(ξ) = κ₀(ξ) + I_k(0)` (Lemma 8.2 (ii): the length of the interval and `m_i` do not depend on `ξ`). -/
theorem H_Ik_map (q L k ξ : ℕ) (hq : 1 ≤ q) :
    Ik q L k ξ = (Ik q L k 0).map (addLeftEmbedding (kappa0 q L ξ)) := by
  unfold Ik
  rw [H_kappa0_zero q L hq]
  split_ifs
  · simp
  · rw [Finset.map_union, Finset.map_add_left_Ico, Finset.map_add_left_Ico]
    congr 1 <;> congr 1 <;> ring

/-- Step 7: `Σ_{κ∈I_k(ξ)} e(gκ/2^D + βξ/2^q) = C_k(g) e(gκ₀(ξ)/2^D + βξ/2^q)`. -/
theorem H_sum_Ik (q L k ξ D g : ℕ) (β : ℝ) (hq : 1 ≤ q) :
    ∑ κ ∈ Ik q L k ξ, eC ((g : ℝ) * (κ : ℝ) / 2 ^ D + β * ξ / 2 ^ q) =
      H_C q L k D g * eC ((g : ℝ) * (kappa0 q L ξ : ℝ) / 2 ^ D + β * ξ / 2 ^ q) := by
  rw [H_Ik_map q L k ξ hq, Finset.sum_map, H_C, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← H_eC_add]; congr 1
  simp only [addLeftEmbedding, Function.Embedding.coeFn_mk]; push_cast; ring

theorem H_norm_C_le (q L k D g : ℕ) : ‖H_C q L k D g‖ ≤ (Ik q L k 0).card := by
  unfold H_C
  refine (norm_sum_le _ _).trans ?_
  simp [H_norm_eC]

theorem H_C_zero (q L k D : ℕ) : H_C q L k D 0 = (Ik q L k 0).card := by
  simp [H_C, H_eC_zero]

theorem H_Ik_card_pos (q L k ξ : ℕ) : 0 < (Ik q L k ξ).card := by
  rw [Ik_card]; split_ifs <;> positivity

/-! ## The measure `μ` on deep frequencies -/

section Mu
variable (q s L j0 : ℕ)

/-- `c(ξ) = |Ê(ξ)|² 1[ξ ≠ 0, dep(ξ) > j₀]`. -/
noncomputable def H_cw (ξ : ℕ) : ℝ :=
  if j0 < dep q ξ then (if ξ = 0 then 0 else ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2) else 0

theorem H_cw_nonneg (ξ : ℕ) : 0 ≤ H_cw q s L j0 ξ := by
  unfold H_cw; split_ifs <;> positivity

/-- `c(ξ) = (1 − ϖ_{j₀}) W μ(ξ)`. -/
theorem H_cw_eq (hvar : varpi q s L j0 < 1) (hW : 0 < Wsum q (Eset q (hL s L))) (ξ : ℕ) :
    H_cw q s L j0 ξ = (1 - varpi q s L j0) * Wsum q (Eset q (hL s L)) * muDeep q s L j0 ξ := by
  have h1 : 0 < 1 - varpi q s L j0 := by linarith
  unfold H_cw muDeep
  by_cases hd : j0 < dep q ξ <;> by_cases h0 : ξ = 0 <;> simp [hd, h0]; field_simp

/-- `Σ_ξ c(ξ) = (1 − ϖ_{j₀}) W`. -/
theorem H_sum_cw (hW : 0 < Wsum q (Eset q (hL s L))) :
    ∑ ξ ∈ range (2 ^ q), H_cw q s L j0 ξ = (1 - varpi q s L j0) * Wsum q (Eset q (hL s L)) := by
  set W := Wsum q (Eset q (hL s L))
  set f : ℕ → ℝ := fun ξ => ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2
  have hv : varpi q s L j0 * W =
      ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => dep q ξ ≤ j0), f ξ := by
    unfold varpi; exact div_mul_cancel₀ _ hW.ne'
  have hsplit := Finset.sum_filter_add_sum_filter_not ((range (2 ^ q)).erase 0)
    (fun ξ => dep q ξ ≤ j0) f
  have hW' : W = ∑ ξ ∈ (range (2 ^ q)).erase 0, f ξ := rfl
  have h0 : H_cw q s L j0 0 = 0 := by unfold H_cw; simp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by positivity)), h0, zero_add]
  have : ∑ ξ ∈ (range (2 ^ q)).erase 0, H_cw q s L j0 ξ =
      ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => ¬ dep q ξ ≤ j0), f ξ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ξ hξ => ?_)
    have hξ0 : ξ ≠ 0 := Finset.ne_of_mem_erase hξ
    unfold H_cw; simp only [not_le, hξ0, ↓reduceIte]; rfl
  rw [this, sub_mul, one_mul, hv, hW', ← hsplit]; ring

/-- `μ` is a probability measure: `Σ_ξ μ(ξ) = 1`. -/
theorem H_sum_muDeep (hvar : varpi q s L j0 < 1) (hW : 0 < Wsum q (Eset q (hL s L))) :
    ∑ ξ ∈ range (2 ^ q), muDeep q s L j0 ξ = 1 := by
  have h1 : 0 < 1 - varpi q s L j0 := by linarith
  have := H_sum_cw q s L j0 hW
  simp_rw [H_cw_eq q s L j0 hvar hW, ← Finset.mul_sum] at this
  have hne : (1 - varpi q s L j0) * Wsum q (Eset q (hL s L)) ≠ 0 := by positivity
  calc _ = ((1 - varpi q s L j0) * Wsum q (Eset q (hL s L)))⁻¹ *
        ((1 - varpi q s L j0) * Wsum q (Eset q (hL s L)) *
          ∑ ξ ∈ range (2 ^ q), muDeep q s L j0 ξ) := by field_simp
    _ = 1 := by rw [this, inv_mul_cancel₀ hne]

theorem H_muDeep_nonneg (hvar : varpi q s L j0 < 1) (hW : 0 < Wsum q (Eset q (hL s L))) (ξ : ℕ) :
    0 ≤ muDeep q s L j0 ξ := by
  have h1 : 0 < 1 - varpi q s L j0 := by linarith
  unfold muDeep; split_ifs <;> positivity

/-- `|𝔼_μ e(·)| ≤ 1` (used for the boundedness of the `sup` in `S_p^*`). -/
theorem H_norm_muChar_le (hvar : varpi q s L j0 < 1) (hW : 0 < Wsum q (Eset q (hL s L)))
    (D h : ℕ) (β : ℝ) : ‖muChar q s L j0 D h β‖ ≤ 1 := by
  unfold muChar
  refine (norm_sum_le _ _).trans ?_
  rw [← H_sum_muDeep q s L j0 hvar hW]
  refine Finset.sum_le_sum (fun ξ _ => ?_)
  rw [norm_mul, H_norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (H_muDeep_nonneg q s L j0 hvar hW ξ)]

end Mu

/-- Move the average over the deep part of the shell to an average over `μ` (the deep version of (∗) in §9 and steps 6, 7):
if `F(N) ≤ Re Σ_σ a_σ e(g_σ κ(N)/2^D + β_σ ξ_N/2^q) + ε` pointwise, then
`⟨F⟩^{>j₀}_k/(1 − ϖ_{j₀}) ≤ Re Σ_σ a_σ (C_k(g_σ)/#I_k) 𝔼_μ e(g_σκ₀/2^D + β_σξ/2^q) + ε`. -/
theorem H_fiber (q s L j0 D k : ℕ) (hq : 1 ≤ q) (hvar : varpi q s L j0 < 1)
    (hW : 0 < Wsum q (Eset q (hL s L))) {ι : Type*} (S : Finset ι) (a : ι → ℂ) (g : ι → ℕ)
    (β : ι → ℝ) (ε : ℝ) (F : ℤ → ℝ)
    (hF : ∀ N ∈ shell q k, F N ≤
      (∑ σ ∈ S, a σ * eC ((g σ : ℝ) * (kappaN q L N : ℝ) / 2 ^ D +
        β σ * (xiN q L N : ℝ) / 2 ^ q)).re + ε) :
    shAvgDeep q s L k j0 F / (1 - varpi q s L j0) ≤
      (∑ σ ∈ S, a σ * (H_C q L k D (g σ) / ((Ik q L k 0).card : ℂ)) *
        muChar q s L j0 D (g σ) (β σ)).re + ε := by
  set v := varpi q s L j0 with hv_def
  set W := Wsum q (Eset q (hL s L)) with hW_def
  set K : ℝ := ((Ik q L k 0).card : ℝ) with hK_def
  have hK : 0 < K := by rw [hK_def]; exact_mod_cast H_Ik_card_pos q L k 0
  have hv : 0 < 1 - v := by linarith
  have hcardξ : ∀ ξ, ((Ik q L k ξ).card : ℝ) = K := by
    intro ξ; rw [hK_def, Ik_card, Ik_card]
  -- Denominator: `Σ_{N ∈ J_k} w(N) = #I_k · W`
  have hden : ∑ N ∈ shell q k, wN q s L N = K * W := by
    rw [shell_fiber q L hq k]
    have : ∀ ξ ∈ range (2 ^ q), ∑ κ ∈ Ik q L k ξ, wN q s L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) =
        K * (if ξ = 0 then 0 else ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2) := by
      intro ξ hξ
      have hx : ∀ κ ∈ Ik q L k ξ, wN q s L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) =
          (if ξ = 0 then 0 else ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2) := by
        intro κ _
        unfold wN; rw [(xiN_kappaN_of q L ξ (Finset.mem_range.1 hξ) κ).1]
      rw [Finset.sum_congr rfl hx, Finset.sum_const, nsmul_eq_mul, hcardξ]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by positivity))]
    simp only [↓reduceIte, zero_add, hW_def, Wsum]
    exact Finset.sum_congr rfl (fun ξ hξ => by simp [Finset.ne_of_mem_erase hξ])
  -- Numerator
  set Φ : ℕ → ℂ := fun ξ => ∑ σ ∈ S, a σ * H_C q L k D (g σ) *
    eC ((g σ : ℝ) * (kappa0 q L ξ : ℝ) / 2 ^ D + β σ * ξ / 2 ^ q) with hΦ
  have hnum : ∑ N ∈ (shell q k).filter (fun N => j0 < dep q (xiN q L N)), wN q s L N * F N ≤
      ∑ ξ ∈ range (2 ^ q), H_cw q s L j0 ξ * ((Φ ξ).re + K * ε) := by
    rw [Finset.sum_filter]
    calc _ ≤ ∑ N ∈ shell q k, (if j0 < dep q (xiN q L N) then wN q s L N else 0) *
          ((∑ σ ∈ S, a σ * eC ((g σ : ℝ) * (kappaN q L N : ℝ) / 2 ^ D +
            β σ * (xiN q L N : ℝ) / 2 ^ q)).re + ε) := by
          refine Finset.sum_le_sum (fun N hN => ?_)
          split_ifs
          · exact mul_le_mul_of_nonneg_left (hF N hN) (by unfold wN; split_ifs <;> positivity)
          · simp
      _ = _ := by
          rw [shell_fiber q L hq k]
          refine Finset.sum_congr rfl (fun ξ hξ => ?_)
          have hξ' := Finset.mem_range.1 hξ
          have hx : ∀ κ ∈ Ik q L k ξ,
              (if j0 < dep q (xiN q L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ)) then
                wN q s L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) else 0) *
              ((∑ σ ∈ S, a σ * eC ((g σ : ℝ) * (kappaN q L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) : ℝ) / 2 ^ D +
                β σ * (xiN q L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) : ℝ) / 2 ^ q)).re + ε) =
              H_cw q s L j0 ξ * ((∑ σ ∈ S, a σ * eC ((g σ : ℝ) * (κ : ℝ) / 2 ^ D +
                β σ * (ξ : ℝ) / 2 ^ q)).re + ε) := by
            intro κ _
            obtain ⟨h1, h2⟩ := xiN_kappaN_of q L ξ hξ' κ
            unfold wN; rw [h1, h2]; rfl
          rw [Finset.sum_congr rfl hx, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul, hcardξ, ← Complex.re_sum, Finset.sum_comm]
          congr 3
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          rw [← Finset.mul_sum, H_sum_Ik q L k ξ D (g σ) (β σ) hq, mul_assoc]
  -- Computing the right-hand side
  have hkey : ∑ ξ ∈ range (2 ^ q), H_cw q s L j0 ξ * ((Φ ξ).re + K * ε) =
      (1 - v) * W * K * ((∑ σ ∈ S, a σ * (H_C q L k D (g σ) / ((Ik q L k 0).card : ℂ)) *
        muChar q s L j0 D (g σ) (β σ)).re + ε) := by
    have hμ := H_sum_muDeep q s L j0 hvar hW
    simp_rw [H_cw_eq q s L j0 hvar hW]
    have h1 : ∑ ξ ∈ range (2 ^ q), muDeep q s L j0 ξ * (Φ ξ).re =
        (∑ σ ∈ S, a σ * H_C q L k D (g σ) * muChar q s L j0 D (g σ) (β σ)).re := by
      have : ∑ σ ∈ S, a σ * H_C q L k D (g σ) * muChar q s L j0 D (g σ) (β σ) =
          ∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) * Φ ξ := by
        simp only [hΦ, muChar, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun ξ _ => ?_))
        ring
      rw [this, Complex.re_sum]
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      rw [Complex.re_ofReal_mul]
    have h2 : (∑ σ ∈ S, a σ * H_C q L k D (g σ) * muChar q s L j0 D (g σ) (β σ)).re =
        K * (∑ σ ∈ S, a σ * (H_C q L k D (g σ) / ((Ik q L k 0).card : ℂ)) *
          muChar q s L j0 D (g σ) (β σ)).re := by
      rw [← Complex.re_ofReal_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      have hK' : ((Ik q L k 0).card : ℂ) ≠ 0 := by exact_mod_cast (H_Ik_card_pos q L k 0).ne'
      rw [hK_def]; push_cast; field_simp
    calc _ = (1 - v) * W * (∑ ξ ∈ range (2 ^ q), muDeep q s L j0 ξ * (Φ ξ).re +
          K * ε * ∑ ξ ∈ range (2 ^ q), muDeep q s L j0 ξ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun ξ _ => ?_); ring
      _ = _ := by rw [h1, h2, hμ]; ring
  -- Conclusion
  unfold shAvgDeep
  rw [hden]
  have hKW : 0 < K * W := mul_pos hK hW
  rw [div_div, div_le_iff₀ (mul_pos hKW hv)]
  calc _ ≤ ∑ ξ ∈ range (2 ^ q), H_cw q s L j0 ξ * ((Φ ξ).re + K * ε) := hnum
    _ = _ := by rw [hkey]; ring

/-! ## Bounding the error `ϑ_b` (step 4) -/

/-- Errors `err₀ = 2πq2^{−q}`, `err_k = 2πq3^{k−L_p}` (`k ≥ 1`). -/
noncomputable def errK (q k : ℕ) : ℝ :=
  if k = 0 then 2 * Real.pi * q * (2:ℝ) ^ (-(q : ℝ)) else 2 * Real.pi * q * (3:ℝ) ^ ((k : ℝ) - Lp q)

/-- Step 4: if `d_b ≥ 2`, `n_b ≥ L_p + 1` and `#B' ≤ 8q`, then `2π Σ_b |ϑ_b(N)| ≤ err_k` (`N ∈ J_k`). -/
theorem H_err_le {n : ℕ} (q k : ℕ) (hq : 1 ≤ q) (N : ℤ) (hN : N ∈ shell q k) (d nn : Fin n → ℕ)
    (hd : ∀ i, 2 ≤ d i) (hnn : ∀ i, Lp q + 1 ≤ nn i) (hcard : (n : ℝ) ≤ 8 * q) :
    2 * Real.pi * ∑ i, |-(N : ℝ) / (2 ^ (q + d i) * 3 ^ nn i)| ≤ errK q k := by
  set M : ℝ := max 1 ((3:ℝ) ^ k) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hNa := shell_abs q k N hN
  have hLp : (2:ℝ) ^ q < 3 ^ (Lp q + 1) := by exact_mod_cast H_Lp_lt q
  have hterm : ∀ i, |-(N : ℝ) / (2 ^ (q + d i) * 3 ^ nn i)| ≤ M / (8 * 3 ^ (Lp q + 1)) := by
    intro i
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 ^ (q + d i) * 3 ^ nn i)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (2:ℝ) ^ (q + 2) ≤ 2 ^ (q + d i) := pow_le_pow_right₀ (by norm_num) (by linarith [hd i])
    have h2 : (3:ℝ) ^ (Lp q + 1) ≤ 3 ^ nn i := pow_le_pow_right₀ (by norm_num) (hnn i)
    have h3 : (2:ℝ) ^ (q + 2) = 8 * 2 ^ (q - 1) := by
      rw [show q + 2 = (q - 1) + 3 by omega, pow_add]; ring
    calc |(N : ℝ)| * (8 * 3 ^ (Lp q + 1)) ≤ 2 ^ (q - 1) * M * (8 * 3 ^ (Lp q + 1)) :=
          mul_le_mul_of_nonneg_right hNa (by positivity)
      _ = M * (2 ^ (q + 2) * 3 ^ (Lp q + 1)) := by rw [h3]; ring
      _ ≤ M * (2 ^ (q + d i) * 3 ^ nn i) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hsum : ∑ i, |-(N : ℝ) / (2 ^ (q + d i) * 3 ^ nn i)| ≤ n * (M / (8 * 3 ^ (Lp q + 1))) := by
    calc _ ≤ ∑ _i : Fin n, M / (8 * 3 ^ (Lp q + 1)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by simp
  have hpi : 0 < 2 * Real.pi := by positivity
  refine (mul_le_mul_of_nonneg_left hsum hpi.le).trans ?_
  unfold errK
  split_ifs with hk
  · subst hk
    have hM' : M = 1 := by rw [hM]; simp
    rw [hM', Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [show 2 * Real.pi * q * ((2:ℝ) ^ q)⁻¹ = 2 * Real.pi * (q / 2 ^ q) by ring]
    apply mul_le_mul_of_nonneg_left _ hpi.le
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq0 : (0:ℝ) ≤ q := by positivity
    have hn0 : (0:ℝ) ≤ n := by positivity
    calc (n : ℝ) * 2 ^ q ≤ 8 * q * 2 ^ q := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ 8 * q * 3 ^ (Lp q + 1) := mul_le_mul_of_nonneg_left hLp.le (by positivity)
      _ = q * (8 * 3 ^ (Lp q + 1)) := by ring
  · have hM' : M = 3 ^ k := by
      rw [hM]; exact max_eq_right (one_le_pow₀ (by norm_num))
    rw [hM', Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    rw [show 2 * Real.pi * q * ((3:ℝ) ^ k / 3 ^ Lp q) = 2 * Real.pi * (q * 3 ^ k / 3 ^ Lp q) by ring]
    apply mul_le_mul_of_nonneg_left _ hpi.le
    rw [pow_succ]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : (n : ℝ) * 3 ^ k * 3 ^ Lp q ≤ 8 * q * 3 ^ k * 3 ^ Lp q := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    have hpos : (0:ℝ) ≤ q * 3 ^ k * 3 ^ Lp q := by positivity
    have e1 : (q:ℝ) * 3 ^ k * (8 * (3 ^ Lp q * 3)) = 24 * (q * 3 ^ k * 3 ^ Lp q) := by ring
    have e2 : 8 * (q:ℝ) * 3 ^ k * 3 ^ Lp q = 8 * (q * 3 ^ k * 3 ^ Lp q) := by ring
    rw [e1]; linarith

/-! ## Numbering of the swap blocks in the window `B' = {b ∈ ℬ(τ) | d_b ≤ D}` (steps 1–3) -/

section Window
variable (q s L P D : ℕ) (τ : Fin (s - P) → Bool)

/-- `B' = {b ∈ ℬ(τ) | d_b ≤ D}` (`#B' = N_D(τ)`). -/
noncomputable def H_Bw : Finset ℕ := (Bset q s P τ).filter (fun k => db s P k ≤ D)

theorem H_Nd_eq : Nd q s P τ D = (H_Bw q s P D τ).card := rfl

/-- Numbering `Fin #B' → ℕ` of the elements of `B'`. -/
noncomputable def H_b (i : Fin (H_Bw q s P D τ).card) : ℕ :=
  ((H_Bw q s P D τ).equivFin.symm i : ℕ)

/-- `d_b`. -/
noncomputable def H_d (i : Fin (H_Bw q s P D τ).card) : ℕ := db s P (H_b q s P D τ i)

/-- `u_b = −3^{−n_b} mod 2^{d_b}`. -/
noncomputable def H_u (i : Fin (H_Bw q s P D τ).card) : ℤ :=
  (ub (H_d q s P D τ i) (nb q s P τ (H_b q s P D τ i)) : ℤ)

/-- `β_σ = Σ_b σ_b 3^{e_b}/2^{d_b}`. -/
noncomputable def H_β (σ : Fin (H_Bw q s P D τ).card → ℤ) : ℝ :=
  ∑ i, (σ i : ℝ) * 3 ^ (L - nb q s P τ (H_b q s P D τ i)) / 2 ^ H_d q s P D τ i

theorem H_b_mem (i : Fin (H_Bw q s P D τ).card) :
    H_b q s P D τ i ∈ Bset q s P τ ∧ db s P (H_b q s P D τ i) ≤ D :=
  Finset.mem_filter.1 ((H_Bw q s P D τ).equivFin.symm i).2

theorem H_b_swap (i : Fin (H_Bw q s P D τ).card) : IsSwap q s P τ (H_b q s P D τ i) :=
  H_mem_Bset (H_b_mem q s P D τ i).1

theorem H_b_inj : Function.Injective (H_b q s P D τ) := fun _ _ h =>
  (H_Bw q s P D τ).equivFin.symm.injective (Subtype.ext h)

theorem H_d_ge (i : Fin (H_Bw q s P D τ).card) : 2 ≤ H_d q s P D τ i :=
  H_db_ge (H_b_swap q s P D τ i)

theorem H_d_le (i : Fin (H_Bw q s P D τ).card) : H_d q s P D τ i ≤ D := (H_b_mem q s P D τ i).2

theorem H_d_inj : Function.Injective (H_d q s P D τ) := by
  intro i j h
  apply H_b_inj q s P D τ
  have hi := H_swap_pos (H_b_swap q s P D τ i)
  have hj := H_swap_pos (H_b_swap q s P D τ j)
  unfold H_d db at h; omega

theorem H_d_par (i j : Fin (H_Bw q s P D τ).card) : H_d q s P D τ i % 2 = H_d q s P D τ j % 2 := by
  have hi := H_swap_pos (H_b_swap q s P D τ i)
  have hj := H_swap_pos (H_b_swap q s P D τ j)
  unfold H_d db; omega

theorem H_u_odd (i : Fin (H_Bw q s P D τ).card) : H_u q s P D τ i % 2 = 1 :=
  H_ub_odd _ _ (by have := H_d_ge q s P D τ i; omega)

theorem H_card_le : (H_Bw q s P D τ).card ≤ s - P := by
  classical
  calc (H_Bw q s P D τ).card ≤ (Bset q s P τ).card := Finset.card_filter_le _ _
    _ ≤ (range (s - P)).card := by unfold Bset; exact Finset.card_filter_le _ _
    _ = s - P := Finset.card_range _

/-- Pointwise form of steps 1–4: for `N ∈ J_k`,
`Π_{b∈ℬ(τ)} cos² πθ_b(N) ≤ Re Σ_σ P(σ) e(h_σ κ(N)/2^D + β_σ ξ_N/2^q) + err_k`. -/
theorem H_pointwise (k : ℕ) (hτ : τ ∈ Tset q s L P) (hq : 1 ≤ q)
    (hcard : ((H_Bw q s P D τ).card : ℝ) ≤ 8 * q) (N : ℤ) (hN : N ∈ shell q k) :
    riesz q s P τ N ≤
      (∑ σ ∈ Fintype.piFinset (fun _ : Fin (H_Bw q s P D τ).card => H_S3),
        (H_Pσ σ : ℂ) * eC ((H_h D (H_d q s P D τ) (H_u q s P D τ) σ : ℝ) * (kappaN q L N : ℝ) / 2 ^ D +
          H_β q s L P D τ σ * (xiN q L N : ℝ) / 2 ^ q)).re + errK q k := by
  set n := (H_Bw q s P D τ).card with hn_def
  set b := H_b q s P D τ with hb_def
  set d := H_d q s P D τ with hd_def
  set u := H_u q s P D τ with hu_def
  set S := Fintype.piFinset (fun _ : Fin n => H_S3) with hS_def
  set f : ℕ → ℝ := fun k => Real.cos (Real.pi * theta q s P τ k N) ^ 2 with hf_def
  -- Step 1: drop the factors outside the window
  have h1 : riesz q s P τ N ≤ ∏ i, f (b i) := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not (Bset q s P τ) (fun k => db s P k ≤ D) f
    have hA : ∏ i, f (b i) = ∏ k ∈ H_Bw q s P D τ, f k := by
      rw [← Finset.prod_coe_sort (H_Bw q s P D τ) f]
      exact Equiv.prod_comp (H_Bw q s P D τ).equivFin.symm (fun x => f x)
    have hr : riesz q s P τ N = (∏ k ∈ H_Bw q s P D τ, f k) *
        ∏ k ∈ (Bset q s P τ).filter (fun k => ¬ db s P k ≤ D), f k := hsplit.symm
    rw [hA, hr]
    have h0 : 0 ≤ ∏ k ∈ H_Bw q s P D τ, f k := Finset.prod_nonneg (fun _ _ => sq_nonneg _)
    have hle : ∏ k ∈ (Bset q s P τ).filter (fun k => ¬ db s P k ≤ D), f k ≤ 1 :=
      cpt_prod_le_one (fun _ _ => sq_nonneg _) (fun _ _ => Real.cos_sq_le_one _)
    calc _ ≤ (∏ k ∈ H_Bw q s P D τ, f k) * 1 := mul_le_mul_of_nonneg_left hle h0
      _ = _ := mul_one _
  -- Step 2: phase (Lemma 8.3)
  have hphase : ∀ i, ∃ m : ℤ, theta q s P τ (b i) N =
      ((u i : ℝ) * (kappaN q L N : ℝ) + (3:ℝ) ^ (L - nb q s P τ (b i)) * (xiN q L N : ℝ) / 2 ^ q) /
        2 ^ d i - (N : ℝ) / (2 ^ (q + d i) * 3 ^ nb q s P τ (b i)) + m := by
    intro i
    have hsw := H_b_swap q s P D τ i
    obtain ⟨m, hm⟩ := theta_phase q s L P τ (b i) N
      (by have : Lp q + 1 ≤ nb q s P τ (b i) := H_nb_ge τ (b i); omega) (H_nb_le hτ hsw)
      (by have : 2 ≤ db s P (b i) := H_db_ge hsw; omega)
    refine ⟨m, ?_⟩
    rw [hm, hu_def, hd_def, H_u, H_d]; push_cast; rfl
  choose m hm using hphase
  set ϑ : Fin n → ℝ := fun i => -(N : ℝ) / (2 ^ (q + d i) * 3 ^ nb q s P τ (b i)) with hϑ_def
  set main : (Fin n → ℤ) → ℝ := fun σ => (H_h D d u σ : ℝ) * (kappaN q L N : ℝ) / 2 ^ D +
    H_β q s L P D τ σ * (xiN q L N : ℝ) / 2 ^ q with hmain_def
  -- Step 3: `Σ_b σ_b θ_b ≡ h_σ κ/2^D + β_σ ξ/2^q + Σ_b σ_b ϑ_b (mod 1)`
  have hsum : ∀ σ : Fin n → ℤ, ∃ M : ℤ,
      ∑ i, (σ i : ℝ) * theta q s P τ (b i) N = main σ + ∑ i, (σ i : ℝ) * ϑ i + M := by
    intro σ
    obtain ⟨m', hm'⟩ := H_X_int D d u (H_d_le q s P D τ) σ (kappaN q L N)
    refine ⟨m' + ∑ i, σ i * m i, ?_⟩
    have e : ∑ i, (σ i : ℝ) * theta q s P τ (b i) N =
        (kappaN q L N : ℝ) * ∑ i, (σ i : ℝ) * u i / 2 ^ d i +
          H_β q s L P D τ σ * (xiN q L N : ℝ) / 2 ^ q + ∑ i, (σ i : ℝ) * ϑ i +
          ((∑ i, σ i * m i : ℤ) : ℝ) := by
      rw [Finset.mul_sum, H_β, Finset.sum_mul, Finset.sum_div, Int.cast_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      rw [hm i, hϑ_def]; ring
    rw [e, hm', hmain_def]; push_cast; ring
  -- Expansion (§8.3)
  have hexp : ((∏ i, f (b i) : ℝ) : ℂ) =
      ∑ σ ∈ S, (H_Pσ σ : ℂ) * (eC (main σ) * eC (∑ i, (σ i : ℝ) * ϑ i)) := by
    have := H_prod_cos_sq (fun i => theta q s P τ (b i) N)
    rw [show (∏ i, f (b i)) = ∏ i, Real.cos (Real.pi * theta q s P τ (b i) N) ^ 2 from rfl, this]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    obtain ⟨M, hM⟩ := hsum σ
    rw [hM, H_eC_add_int, H_eC_add]
  -- Step 4: error
  have hbound : (∑ σ ∈ S, (H_Pσ σ : ℂ) * (eC (main σ) * eC (∑ i, (σ i : ℝ) * ϑ i))).re ≤
      (∑ σ ∈ S, (H_Pσ σ : ℂ) * eC (main σ)).re + 2 * Real.pi * ∑ i, |ϑ i| := by
    have hsplit : ∑ σ ∈ S, (H_Pσ σ : ℂ) * (eC (main σ) * eC (∑ i, (σ i : ℝ) * ϑ i)) =
        ∑ σ ∈ S, (H_Pσ σ : ℂ) * eC (main σ) +
          ∑ σ ∈ S, (H_Pσ σ : ℂ) * eC (main σ) * (eC (∑ i, (σ i : ℝ) * ϑ i) - 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun σ _ => ?_); ring
    rw [hsplit, Complex.add_re]
    apply add_le_add_right
    calc _ ≤ ‖∑ σ ∈ S, (H_Pσ σ : ℂ) * eC (main σ) * (eC (∑ i, (σ i : ℝ) * ϑ i) - 1)‖ :=
          Complex.re_le_norm _
      _ ≤ ∑ σ ∈ S, ‖(H_Pσ σ : ℂ) * eC (main σ) * (eC (∑ i, (σ i : ℝ) * ϑ i) - 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ σ ∈ S, H_Pσ σ * (2 * Real.pi * ∑ i, |ϑ i|) := by
          refine Finset.sum_le_sum (fun σ hσ => ?_)
          rw [norm_mul, norm_mul, H_norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (H_Pσ_nonneg σ)]
          apply mul_le_mul_of_nonneg_left _ (H_Pσ_nonneg σ)
          refine (H_norm_eC_sub_one _).trans ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
          rw [abs_mul]
          have := H_abs_le_one hσ i
          have h' : |(σ i : ℝ)| ≤ 1 := by exact_mod_cast this
          calc |(σ i : ℝ)| * |ϑ i| ≤ 1 * |ϑ i| := mul_le_mul_of_nonneg_right h' (abs_nonneg _)
            _ = |ϑ i| := one_mul _
      _ = 2 * Real.pi * ∑ i, |ϑ i| := by rw [← Finset.sum_mul, H_sum_Pσ, one_mul]
  have herr : 2 * Real.pi * ∑ i, |ϑ i| ≤ errK q k :=
    H_err_le q k hq N hN d (fun i => nb q s P τ (b i)) (H_d_ge q s P D τ)
      (fun i => H_nb_ge τ (b i)) hcard
  calc riesz q s P τ N ≤ ∏ i, f (b i) := h1
    _ = (((∏ i, f (b i) : ℝ) : ℂ)).re := (Complex.ofReal_re _).symm
    _ ≤ _ := by rw [hexp]; linarith [hbound, herr]

end Window

/-! ## Steps 5, 8: the range of `β_σ` and Hölder -/

/-- Step 5: `|β_σ| ≤ #B' · 2^{h_L−1}/3 ≤ q2^{h_L}` (Lemma 8.4, `#B' ≤ 6q`). -/
theorem H_beta_mem (q s L P D : ℕ) (τ : Fin (s - P) → Bool) (hτ : τ ∈ Tset q s L P)
    (hcard : ((H_Bw q s P D τ).card : ℝ) ≤ 6 * q)
    (σ : Fin (H_Bw q s P D τ).card → ℤ)
    (hσ : σ ∈ Fintype.piFinset (fun _ : Fin (H_Bw q s P D τ).card => H_S3)) :
    H_β q s L P D τ σ ∈ Set.Icc (-((q : ℝ) * (2:ℝ) ^ hL s L)) ((q : ℝ) * (2:ℝ) ^ hL s L) := by
  rw [Set.mem_Icc, ← abs_le]
  have hterm : ∀ i, |(σ i : ℝ) * 3 ^ (L - nb q s P τ (H_b q s P D τ i)) / 2 ^ H_d q s P D τ i| ≤
      (2:ℝ) ^ hL s L / 6 := by
    intro i
    have hsw := H_b_swap q s P D τ i
    have hdb := dist_bound q s L P τ (H_b q s P D τ i) hsw (H_nb_le hτ hsw)
    rw [Real.rpow_sub_one (by norm_num)] at hdb
    have h' : |(σ i : ℝ)| ≤ 1 := by exact_mod_cast H_abs_le_one hσ i
    rw [mul_div_assoc, abs_mul,
      abs_of_nonneg (a := (3:ℝ) ^ (L - nb q s P τ (H_b q s P D τ i)) / 2 ^ H_d q s P D τ i)
        (by positivity)]
    calc |(σ i : ℝ)| * ((3:ℝ) ^ (L - nb q s P τ (H_b q s P D τ i)) / 2 ^ H_d q s P D τ i)
        ≤ 1 * ((2:ℝ) ^ hL s L / 2 / 3) :=
          mul_le_mul h' hdb (by positivity) zero_le_one
      _ = (2:ℝ) ^ hL s L / 6 := by ring
  unfold H_β
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |(σ i : ℝ) * 3 ^ (L - nb q s P τ (H_b q s P D τ i)) / 2 ^ H_d q s P D τ i|
      ≤ ∑ _i : Fin (H_Bw q s P D τ).card, (2:ℝ) ^ hL s L / 6 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((H_Bw q s P D τ).card : ℝ) * ((2:ℝ) ^ hL s L / 6) := by simp
    _ ≤ (6 * q) * ((2:ℝ) ^ hL s L / 6) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (q : ℝ) * (2:ℝ) ^ hL s L := by ring

/-- Per-tail estimate (steps 1–8): for `τ ∈ 𝒯`,
`⟨Π_{b∈ℬ(τ)} cos² πθ_b⟩^{>j₀}_k/(1 − ϖ_{j₀}) ≤ 2^{−N_D(τ)} + S_p^*(B)^{1/p} φ_p^{N_D(τ)} + err_k`. -/
theorem H_tail (q s L P j0 D k : ℕ) (p : ℝ) (hp : 2 ≤ p) (τ : Fin (s - P) → Bool)
    (hτ : τ ∈ Tset q s L P) (hq : 1 ≤ q) (hcard : ((H_Bw q s P D τ).card : ℝ) ≤ 6 * q)
    (hvar : varpi q s L j0 < 1) (hW : 0 < Wsum q (Eset q (hL s L))) :
    shAvgDeep q s L k j0 (riesz q s P τ) / (1 - varpi q s L j0) ≤
      (2:ℝ) ^ (-(Nd q s P τ D : ℝ)) +
        Sstar q s L j0 D p (q * (2:ℝ) ^ hL s L) ^ (1 / p) * phiP p ^ Nd q s P τ D + errK q k := by
  set n := (H_Bw q s P D τ).card with hn_def
  set d := H_d q s P D τ with hd_def
  set u := H_u q s P D τ with hu_def
  set S := Fintype.piFinset (fun _ : Fin n => H_S3) with hS_def
  set B : ℝ := (q : ℝ) * (2:ℝ) ^ hL s L with hB_def
  have hKpos : 0 < (Ik q L k 0).card := H_Ik_card_pos q L k 0
  have hK' : ((Ik q L k 0).card : ℂ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hcard8 : (n : ℝ) ≤ 8 * q := by linarith [(Nat.cast_nonneg q : (0:ℝ) ≤ q)]
  have hfib := H_fiber q s L j0 D k hq hvar hW S (fun σ => (H_Pσ σ : ℂ)) (H_h D d u)
    (H_β q s L P D τ) (errK q k) (riesz q s P τ)
    (fun N hN => H_pointwise q s L P D τ k hτ hq hcard8 N hN)
  refine hfib.trans ?_
  rw [H_Nd_eq, ← hn_def]
  have h0mem := H_zero_mem n
  rw [← Finset.add_sum_erase S _ h0mem, Complex.add_re]
  -- The `σ = 0` term is `2^{−n}`
  have hterm0 : ((H_Pσ (0 : Fin n → ℤ) : ℂ) *
      (H_C q L k D (H_h D d u 0) / ((Ik q L k 0).card : ℂ)) *
        muChar q s L j0 D (H_h D d u 0) (H_β q s L P D τ 0)).re = (2:ℝ) ^ (-(n : ℝ)) := by
    have hβ0 : H_β q s L P D τ 0 = 0 := by simp [H_β]
    have hT0 : muChar q s L j0 D 0 0 = 1 := by
      simp only [muChar, Nat.cast_zero, zero_mul, zero_div, add_zero, H_eC_zero, mul_one]
      rw [← Complex.ofReal_sum, H_sum_muDeep q s L j0 hvar hW, Complex.ofReal_one]
    rw [hβ0, H_h_zero, hT0, H_C_zero, div_self hK', mul_one, mul_one, H_Pσ_zero,
      Complex.ofReal_re, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [hterm0]
  -- The `σ ≠ 0` terms: Hölder and injectivity
  have hholder := H_holder p (by linarith) D (H_h D d u)
    (fun σ hσ σ' hσ' h => H_h_injOn D d u (H_d_ge q s P D τ) (H_d_inj q s P D τ)
      (H_d_par q s P D τ) (H_u_odd q s P D τ) (H_d_le q s P D τ)
      (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hσ)))
      (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hσ'))) h)
    (fun σ hσ => Finset.mem_Ico.2 ⟨Nat.one_le_iff_ne_zero.2
      (H_h_ne_zero D d u (H_d_ge q s P D τ) (H_d_inj q s P D τ) (H_d_par q s P D τ)
        (H_u_odd q s P D τ) (H_d_le q s P D τ) σ (Finset.mem_of_mem_erase hσ)
        (Finset.ne_of_mem_erase hσ)), H_h_lt D d u σ⟩)
    (fun σ => ‖muChar q s L j0 D (H_h D d u σ) (H_β q s L P D τ σ)‖) (fun σ => norm_nonneg _)
    (fun h => ⨆ β : Set.Icc (-B) B, ‖muChar q s L j0 D h β‖ ^ p)
    (fun h => Real.iSup_nonneg (fun β => Real.rpow_nonneg (norm_nonneg _) _))
    (by
      intro σ hσ
      have hbdd : BddAbove (Set.range (fun β : Set.Icc (-B) B =>
          ‖muChar q s L j0 D (H_h D d u σ) β‖ ^ p)) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨β, rfl⟩
        exact Real.rpow_le_one (norm_nonneg _) (H_norm_muChar_le q s L j0 hvar hW _ _ _)
          (by linarith)
      exact le_ciSup (f := fun β : Set.Icc (-B) B => ‖muChar q s L j0 D (H_h D d u σ) β‖ ^ p) hbdd
        ⟨H_β q s L P D τ σ, H_beta_mem q s L P D τ hτ hcard σ (Finset.mem_of_mem_erase hσ)⟩)
  have hSstar : Sstar q s L j0 D p B =
      ∑ h ∈ Ico 1 (2 ^ D), ⨆ β : Set.Icc (-B) B, ‖muChar q s L j0 D h β‖ ^ p := rfl
  rw [← hSstar] at hholder
  have hrest : (∑ σ ∈ S.erase 0, (H_Pσ σ : ℂ) *
      (H_C q L k D (H_h D d u σ) / ((Ik q L k 0).card : ℂ)) *
        muChar q s L j0 D (H_h D d u σ) (H_β q s L P D τ σ)).re ≤
      ∑ σ ∈ S.erase 0, H_Pσ σ * ‖muChar q s L j0 D (H_h D d u σ) (H_β q s L P D τ σ)‖ := by
    rw [Complex.re_sum]
    refine Finset.sum_le_sum (fun σ _ => ?_)
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (H_Pσ_nonneg σ),
      norm_div, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hKr : (0:ℝ) < (Ik q L k 0).card := by exact_mod_cast hKpos
    calc H_Pσ σ * (‖H_C q L k D (H_h D d u σ)‖ / ((Ik q L k 0).card : ℝ)) ≤ H_Pσ σ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (H_Pσ_nonneg σ)
          rw [div_le_one hKr]; exact H_norm_C_le q L k D _
      _ = H_Pσ σ := mul_one _
  have := hrest.trans hholder
  linarith

/-! ## Proposition 10.2 -/

/-- Proposition 10.2: let `D ≥ 2`, `p ≥ 2`, `B = q2^{h_L}`. For every shell `0 ≤ k ≤ L`,
`A_k^{>j₀}/(1 − ϖ_{j₀}) ≤ 𝔼_τ 2^{−N_D} + S_p^*(B)^{1/p} 𝔼_τ φ_p^{N_D} + err_k`. -/
theorem holder (δ : ℝ) (s q L P j0 D k : ℕ) (p : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3)
    (hsq1 : 1 < (s : ℝ) / q) (hsq2 : (s : ℝ) / q ≤ 1.94) (hq : 20 ≤ q) (hR : Rdelta δ s q L P)
    (hD : 2 ≤ D) (hp : 2 ≤ p) (hk : k ≤ L) (hvar : varpi q s L j0 < 1)
    (hW : 0 < Wsum q (Eset q (hL s L))) :
    AkDeep q s L P k j0 / (1 - varpi q s L j0) ≤
      ETail q s L P D (fun n => (2:ℝ) ^ (-(n : ℝ))) +
        Sstar q s L j0 D p (q * (2:ℝ) ^ hL s L) ^ (1 / p) * ETail q s L P D (fun n => phiP p ^ n) +
        errK q k := by
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0:ℝ) < q := by positivity
  have hs : (s : ℝ) ≤ 1.94 * q := by rwa [div_le_iff₀ hqpos] at hsq2
  have hne : (Tset q s L P).Nonempty := hR.2.2.2.2.2.1
  have hTpos : (0:ℝ) < (Tset q s L P).card := by exact_mod_cast hne.card_pos
  have hv : 0 < 1 - varpi q s L j0 := by linarith
  set X := Sstar q s L j0 D p (q * (2:ℝ) ^ hL s L) ^ (1 / p) with hX
  -- Steps 1–8: per-tail estimate
  have htail : ∀ τ ∈ Tset q s L P,
      shAvgDeep q s L k j0 (riesz q s P τ) / (1 - varpi q s L j0) ≤
        (2:ℝ) ^ (-(Nd q s P τ D : ℝ)) + X * phiP p ^ Nd q s P τ D + errK q k := by
    intro τ hτ
    have hc : ((H_Bw q s P D τ).card : ℝ) ≤ 6 * q := by
      have h1 : (H_Bw q s P D τ).card ≤ s - P := H_card_le q s P D τ
      have h2 : ((H_Bw q s P D τ).card : ℝ) ≤ s := by exact_mod_cast h1.trans (Nat.sub_le s P)
      linarith
    exact H_tail q s L P j0 D k p hp τ hτ hq1 hc hvar hW
  -- Step 9: average over tails
  have hsum : ∑ τ ∈ Tset q s L P, shAvgDeep q s L k j0 (riesz q s P τ) ≤
      (1 - varpi q s L j0) * ∑ τ ∈ Tset q s L P,
        ((2:ℝ) ^ (-(Nd q s P τ D : ℝ)) + X * phiP p ^ Nd q s P τ D + errK q k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun τ hτ => ?_)
    have := htail τ hτ
    rw [div_le_iff₀ hv] at this
    linarith
  unfold AkDeep ETail
  rw [div_div, div_le_iff₀ (mul_pos hTpos hv)]
  calc _ ≤ _ := hsum
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
      field_simp

end Collatz.M1
