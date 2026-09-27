import CollatzProof.M1.I_Four

/-!
# Auxiliary results for §11.1: expansion of the rounding (Lemma 11.1), expansion of `μ̂` (Lemma 11.2), upper bound on `𝔼_μ e(hκ₀/2^D + βξ/2^q)`

- `I_psi q D h j = ψ̂_h(j) = 2^{-q} Σ_{ℓ<2^q} e(−n_jℓ/M)` (`n_j = h + 2^D j`, `M = 2^{q+D}`).
- `I_kk q θ v = k_θ(v) = 2^{-q} Σ_{ξ<2^q} e((θ − v/2^q)ξ)`.
- `I_theta q D L h j β = θ_j(β) = n_j3^L/M + β/2^q`.
- `‖𝔼_μ e(hκ₀/2^D + βξ/2^q)‖ ≤ Σ_{j,v} |ψ̂_h(j)||k_{θ_j(β)}(v)| A ϱ_E(v)` (`I_muChar_le`, step 2 of Proposition 11.3).
- Kernel bounds: `|ψ̂_h(j)| ≤ w(n_j)`, `|k_{θ_j(β)}(v)| ≤ K(v, n_j)` (`|β| ≤ B`), `Σ_j|ψ̂_h(j)| ≤ q+2`, `Σ_v|k_θ(v)| ≤ q+2`.
-/

namespace Collatz.M1

open Finset

/-- `ψ̂_h(j)`. -/
noncomputable def I_psi (q D h j : ℕ) : ℂ :=
  ((2 ^ q : ℕ) : ℂ)⁻¹ * ∑ l ∈ range (2 ^ q), eC ((-(((h + 2 ^ D * j : ℕ) : ℝ) / 2 ^ (q + D))) * l)

/-- `k_θ(v)`. -/
noncomputable def I_kk (q : ℕ) (θ : ℝ) (v : ℕ) : ℂ :=
  ((2 ^ q : ℕ) : ℂ)⁻¹ * ∑ ξ ∈ range (2 ^ q), eC ((θ - v / 2 ^ q) * ξ)

/-- `θ_j(β)`. -/
noncomputable def I_theta (q D L h j : ℕ) (β : ℝ) : ℝ :=
  ((h + 2 ^ D * j : ℕ) : ℝ) * 3 ^ L / 2 ^ (q + D) + β / 2 ^ q

/-! ## Lemmas 11.1 and 11.2 -/

/-- Lemma 11.1 (expansion of the rounding): `e(h⌊U/2^q⌋/2^D) = Σ_j ψ̂_h(j) e(n_jU/M)`. -/
lemma I_round_expand (q D h U : ℕ) :
    eC ((h : ℝ) * ((U / 2 ^ q : ℕ) : ℝ) / 2 ^ D) =
      ∑ j ∈ range (2 ^ q), I_psi q D h j * eC (((h + 2 ^ D * j : ℕ) : ℝ) * U / 2 ^ (q + D)) := by
  unfold I_psi
  simp_rw [mul_assoc, sum_mul]
  rw [← mul_sum, sum_comm]
  have hterm : ∀ l ∈ range (2 ^ q), ∑ j ∈ range (2 ^ q),
      eC ((-(((h + 2 ^ D * j : ℕ) : ℝ) / 2 ^ (q + D))) * l) *
        eC (((h + 2 ^ D * j : ℕ) : ℝ) * U / 2 ^ (q + D)) =
      eC ((h : ℝ) * (((U : ℤ) - l : ℤ) : ℝ) / 2 ^ (q + D)) *
        (if (2 : ℤ) ^ q ∣ ((U : ℤ) - l) then (2 : ℂ) ^ q else 0) := by
    intro l _
    rw [← I_sum_eC_pow, mul_sum]
    apply sum_congr rfl; intro j _
    rw [← I_eC_add, ← I_eC_add]; congr 1
    push_cast; rw [pow_add]; field_simp; ring
  rw [sum_congr rfl hterm]
  rw [sum_eq_single (U % 2 ^ q)]
  · have hd : (2 : ℤ) ^ q ∣ ((U : ℤ) - ((U % 2 ^ q : ℕ) : ℤ)) := by
      refine ⟨((U / 2 ^ q : ℕ) : ℤ), ?_⟩
      have := Nat.mod_add_div U (2 ^ q)
      have h' : ((U : ℕ) : ℤ) = ((U % 2 ^ q : ℕ) : ℤ) + 2 ^ q * ((U / 2 ^ q : ℕ) : ℤ) := by
        exact_mod_cast this.symm
      rw [h']; ring
    rw [if_pos hd]
    have harg : (h : ℝ) * (((U : ℤ) - ((U % 2 ^ q : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ (q + D) =
        (h : ℝ) * ((U / 2 ^ q : ℕ) : ℝ) / 2 ^ D := by
      have := Nat.mod_add_div U (2 ^ q)
      have h' : ((U : ℕ) : ℝ) = ((U % 2 ^ q : ℕ) : ℝ) + 2 ^ q * ((U / 2 ^ q : ℕ) : ℝ) := by
        exact_mod_cast this.symm
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h', pow_add]; field_simp; ring
    rw [harg]; push_cast; field_simp
  · intro l hl hne
    rw [if_neg, mul_zero]
    intro hd
    apply hne
    have hmod : l ≡ U [MOD 2 ^ q] := by
      rw [Nat.modEq_iff_dvd]; push_cast; exact hd
    rw [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hl)] at hmod
    exact hmod
  · intro h; exact absurd (mem_range.mpr (Nat.mod_lt U (by positivity))) h

/-- The first half of Lemma 11.2: if `ξ < 2^q`, then `e(θξ) = Σ_{v<2^q} k_θ(v) e(vξ/2^q)`. -/
lemma I_kk_expand (q : ℕ) (θ : ℝ) (ξ : ℕ) (hξ : ξ < 2 ^ q) :
    eC (θ * ξ) = ∑ v ∈ range (2 ^ q), I_kk q θ v * eC ((v : ℝ) * ξ / 2 ^ q) := by
  unfold I_kk
  simp_rw [mul_assoc, sum_mul]
  rw [← mul_sum, sum_comm]
  have hterm : ∀ ξ' ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q),
      eC ((θ - v / 2 ^ q) * ξ') * eC ((v : ℝ) * ξ / 2 ^ q) =
      eC (θ * ξ') * (if (2 : ℤ) ^ q ∣ ((ξ : ℤ) - ξ') then (2 : ℂ) ^ q else 0) := by
    intro ξ' _
    rw [← I_sum_eC_pow, mul_sum]
    apply sum_congr rfl; intro v _
    rw [← I_eC_add, ← I_eC_add]; congr 1
    push_cast; field_simp; ring
  rw [sum_congr rfl hterm, sum_eq_single ξ]
  · rw [if_pos (by simp)]; push_cast; field_simp
  · intro ξ' hξ' hne
    rw [if_neg, mul_zero]
    intro hd
    apply hne
    have hmod : ξ' ≡ ξ [MOD 2 ^ q] := by
      rw [Nat.modEq_iff_dvd]; push_cast; exact hd
    rw [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hξ'), Nat.mod_eq_of_lt hξ] at hmod
    exact hmod
  · intro h; exact absurd (mem_range.mpr hξ) h

/-- Expansion of the phase: if `ξ < 2^q`, then
`e(hκ₀(ξ)/2^D + βξ/2^q) = Σ_{j,v} ψ̂_h(j) e(n_j2^{q−1}/M) k_{θ_j(β)}(v) e(vξ/2^q)`. -/
lemma I_phase_expand (q D L h : ℕ) (β : ℝ) (ξ : ℕ) (hξ : ξ < 2 ^ q) :
    eC ((h : ℝ) * (kappa0 q L ξ : ℝ) / 2 ^ D + β * ξ / 2 ^ q) =
      ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q),
        I_psi q D h j * eC (((h + 2 ^ D * j : ℕ) : ℝ) * 2 ^ (q - 1) / 2 ^ (q + D)) *
          I_kk q (I_theta q D L h j β) v * eC ((v : ℝ) * ξ / 2 ^ q) := by
  have hk : (kappa0 q L ξ : ℝ) = (((3 ^ L * ξ + 2 ^ (q - 1)) / 2 ^ q : ℕ) : ℝ) := by
    unfold kappa0; push_cast; rfl
  rw [I_eC_add, hk, I_round_expand q D h (3 ^ L * ξ + 2 ^ (q - 1)), sum_mul]
  apply sum_congr rfl; intro j _
  have e1 : eC (((h + 2 ^ D * j : ℕ) : ℝ) * ((3 ^ L * ξ + 2 ^ (q - 1) : ℕ) : ℝ) / 2 ^ (q + D)) *
      eC (β * ξ / 2 ^ q) =
      eC (((h + 2 ^ D * j : ℕ) : ℝ) * 2 ^ (q - 1) / 2 ^ (q + D)) *
        eC (I_theta q D L h j β * ξ) := by
    rw [← I_eC_add, ← I_eC_add]; congr 1; unfold I_theta; push_cast; field_simp; ring
  rw [mul_assoc, e1, I_kk_expand q _ ξ hξ, mul_sum, mul_sum]
  apply sum_congr rfl; intro v _; ring

/-- Step 2 of Proposition 11.3: `‖𝔼_μ e(hκ₀/2^D + βξ/2^q)‖ ≤ Σ_{j,v} |ψ̂_h(j)||k_{θ_j(β)}(v)| A ϱ_E(v)`. -/
lemma I_muChar_le (q s L j0 D h : ℕ) (β A : ℝ)
    (hA : ∀ v : ℕ, ‖∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) * eC ((v : ℝ) * ξ / 2 ^ q)‖ ≤
      A * rhoE q s L j0 v) :
    ‖muChar q s L j0 D h β‖ ≤ ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q),
      ‖I_psi q D h j‖ * ‖I_kk q (I_theta q D L h j β) v‖ * (A * rhoE q s L j0 v) := by
  unfold muChar
  have hexp : ∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) *
      eC ((h : ℝ) * (kappa0 q L ξ : ℝ) / 2 ^ D + β * ξ / 2 ^ q) =
      ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q),
        (I_psi q D h j * eC (((h + 2 ^ D * j : ℕ) : ℝ) * 2 ^ (q - 1) / 2 ^ (q + D)) *
          I_kk q (I_theta q D L h j β) v) *
        ∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) * eC ((v : ℝ) * ξ / 2 ^ q) := by
    rw [sum_congr rfl (fun ξ hξ => by rw [I_phase_expand q D L h β ξ (mem_range.mp hξ)])]
    simp_rw [mul_sum]
    rw [sum_comm]; apply sum_congr rfl; intro j _
    rw [sum_comm]; apply sum_congr rfl; intro v _
    apply sum_congr rfl; intro ξ _; ring
  rw [hexp]
  refine le_trans (norm_sum_le _ _) (sum_le_sum fun j _ => ?_)
  refine le_trans (norm_sum_le _ _) (sum_le_sum fun v _ => ?_)
  rw [norm_mul, norm_mul, norm_mul, I_norm_eC, mul_one]
  exact mul_le_mul_of_nonneg_left (hA v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ## Kernel bounds -/

lemma I_psi_le (q D h j : ℕ) :
    ‖I_psi q D h j‖ ≤ I_kf (2 ^ q * I_nd (((h + 2 ^ D * j : ℕ) : ℝ) / 2 ^ (q + D))) := by
  have := I_dirichlet (2 ^ q) (by positivity) (-(((h + 2 ^ D * j : ℕ) : ℝ) / 2 ^ (q + D)))
  unfold I_psi
  rw [I_nd_neg] at this
  push_cast at this ⊢
  exact this

lemma I_kk_le (q : ℕ) (θ : ℝ) (v : ℕ) :
    ‖I_kk q θ v‖ ≤ I_kf (2 ^ q * I_nd (θ - v / 2 ^ q)) := by
  have := I_dirichlet (2 ^ q) (by positivity) (θ - v / 2 ^ q)
  unfold I_kk
  push_cast at this ⊢
  exact this

/-- If `|β| ≤ B`, then `|k_{θ_j(β)}(v)| ≤ K(v, n_j) = I_kf(2^q‖(n_j3^L/2^D − v)/2^q‖ − B)`. -/
lemma I_kk_theta_le (q D L h j : ℕ) (β B : ℝ) (hβ : |β| ≤ B) (v : ℕ) :
    ‖I_kk q (I_theta q D L h j β) v‖ ≤
      I_kf (2 ^ q * I_nd ((((h + 2 ^ D * j : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q) - B) := by
  refine le_trans (I_kk_le q _ v) (I_kf_anti ?_)
  set y0 := ((((h + 2 ^ D * j : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q)
  have hy : I_theta q D L h j β - v / 2 ^ q = y0 + β / 2 ^ q := by
    unfold I_theta; simp only [y0]; rw [pow_add]; field_simp; ring
  rw [hy]
  have := I_nd_add_le y0 (β / 2 ^ q)
  have h2 : (0 : ℝ) < 2 ^ q := by positivity
  rw [abs_div, abs_of_pos h2] at this
  have : 2 ^ q * I_nd y0 ≤ 2 ^ q * I_nd (y0 + β / 2 ^ q) + |β| := by
    have := mul_le_mul_of_nonneg_left this h2.le
    rw [mul_add, mul_div_cancel₀ _ h2.ne'] at this
    exact this
  linarith

/-- `Σ_j |ψ̂_h(j)| ≤ q + 2` (`q ≥ 4`). -/
lemma I_psi_sum_le (q D h : ℕ) (hq : 4 ≤ q) :
    ∑ j ∈ range (2 ^ q), ‖I_psi q D h j‖ ≤ q + 2 := by
  refine le_trans (sum_le_sum fun j _ => I_psi_le q D h j) ?_
  have := I_kernel_sum q hq (-(h : ℝ) / 2 ^ D)
  refine le_of_eq_of_le (sum_congr rfl fun j _ => ?_) this
  congr 2
  rw [← I_nd_neg]; congr 1
  push_cast; rw [pow_add]; field_simp; ring

/-- `Σ_v |k_θ(v)| ≤ q + 2` (`q ≥ 4`). -/
lemma I_kk_sum_le (q : ℕ) (hq : 4 ≤ q) (θ : ℝ) :
    ∑ v ∈ range (2 ^ q), ‖I_kk q θ v‖ ≤ q + 2 := by
  refine le_trans (sum_le_sum fun v _ => I_kk_le q θ v) ?_
  have := I_kernel_sum q hq (2 ^ q * θ)
  refine le_of_eq_of_le (sum_congr rfl fun v _ => ?_) this
  congr 3
  field_simp

end Collatz.M1
