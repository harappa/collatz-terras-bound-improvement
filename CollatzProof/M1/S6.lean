import CollatzProof.M1.Counting
import CollatzProof.M1.E_Model
import CollatzProof.M1.E_Binom

/-! # §6: Counting swap blocks

The auxiliary lemmas are in `E_Model.lean` (properties of the constants, the independent-letter model, Lemma 6.1) and `E_Binom.lean` (the mode of the binomial distribution). -/

namespace Collatz.M1

open Finset

/-! ## Auxiliary: bounds over tail words (steps 1 and 2 of Lemma 6.2) -/

open Classical in
/-- On a surviving tail, the factor of block `k` (positions `(2k−1, 2k)`) is `γ` if it is a swap block and 1 otherwise. -/
theorem E_blk_swap (q s P : ℕ) (γ : ℝ) (τ : Fin (s - P) → Bool) (hS : SurvW (hp q P) τ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk2 : 2 * k + 1 ≤ s - P) :
    E_blk γ (hp q P) τ (2 * k - 1) = if IsSwap q s P τ k then γ else 1 := by
  unfold E_blk
  rw [if_pos ⟨hS _ (by omega) (by omega), hS _ (by omega) (by omega)⟩]
  have hiff : (1 ≤ hw (hp q P) τ (2 * k - 1) ∧ E_xa τ (2 * k - 1) ≠ E_xa τ (2 * k - 1 + 1)) ↔
      IsSwap q s P τ k := by
    unfold IsSwap E_xa
    rw [dif_pos (show 2 * k - 1 < s - P by omega), dif_pos (show 2 * k - 1 + 1 < s - P by omega)]
    have hfin : (⟨2 * k - 1 + 1, (by omega : 2 * k - 1 + 1 < s - P)⟩ : Fin (s - P)) =
        ⟨2 * k, by omega⟩ := Fin.ext (by simp; omega)
    rw [hfin]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, hk1, h2, h1⟩
    · rintro ⟨_, _, h2, h1⟩; exact ⟨h1, h2⟩
  by_cases hsw : IsSwap q s P τ k
  · rw [if_pos (hiff.2 hsw), if_pos hsw]
  · rw [if_neg (mt hiff.1 hsw), if_neg hsw]

/-- Steps 1 and 2: on a surviving tail, `γ^{N_d(τ)} ≤ Π_{k∈𝒦} φ_γ(H_k, b_k)` (the window is the blocks `k₀, …, k₀+m−1`). -/
theorem E_W_ge (q s P : ℕ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (τ : Fin (s - P) → Bool)
    (hS : SurvW (hp q P) τ) (d k₀ m : ℕ) (hk₀ : 1 ≤ k₀) (hm : 2 * k₀ - 1 + 2 * m ≤ s - P)
    (hd : s - P ≤ 2 * k₀ - 1 + d) :
    γ ^ (Nd q s P τ d) ≤ E_W γ (hp q P) τ (2 * k₀ - 1) m := by
  classical
  have e : E_W γ (hp q P) τ (2 * k₀ - 1) m =
      ∏ i ∈ range m, (if IsSwap q s P τ (k₀ + i) then γ else 1) := by
    unfold E_W
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show 2 * k₀ - 1 + 2 * i = 2 * (k₀ + i) - 1 by omega]
    convert E_blk_swap q s P γ τ hS (k₀ + i) (by omega) (by omega)
  rw [e, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  apply pow_le_pow_of_le_one hγ0 hγ1
  unfold Nd
  apply Finset.card_le_card_of_injOn (fun i => k₀ + i)
  · intro i hi
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨_, hsw⟩ := hi
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold Bset
      rw [Finset.mem_filter, Finset.mem_range]
      obtain ⟨h, _⟩ := hsw
      exact ⟨by omega, ⟨h, by assumption⟩⟩
    · unfold db; omega
  · intro a _ b _ hab
    simpa using hab

/-- Lemma 6.2 (window count): for `γ ∈ [1/2, 1]`, `2 ≤ d ≤ t − 1`, `h_L ≥ 0`, `𝒯 ≠ ∅`,
`𝔼_τ γ^{N_d(τ)} ≤ t(t−1) Θ_γ(ρ̄)^{⌊(d−1)/2⌋}`. -/
theorem window_count (q s L P : ℕ) (γ : ℝ) (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) (d : ℕ) (hd1 : 2 ≤ d)
    (hd2 : d ≤ s - P - 1) (hL0 : 0 ≤ hL s L) (hne : (Tset q s L P).Nonempty) :
    ETail q s L P d (fun n => γ ^ n) ≤
      ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) * Theta γ (rhoBar q s L P) ^ ((d - 1) / 2) := by
  classical
  have hγ0 : 0 ≤ γ := by linarith
  have ht3 : 3 ≤ s - P := by omega
  -- properties of the elements of 𝒯
  have hmemT : ∀ τ ∈ Tset q s L P, τ ⟨0, by omega⟩ = true ∧ ones τ (s - P) = L - Lp q ∧
      SurvW (hp q P) τ := by
    intro τ hτ
    simp only [Tset, Finset.mem_filter] at hτ
    exact ⟨hτ.2.1 (by omega), hτ.2.2.1, hτ.2.2.2⟩
  obtain ⟨τ₀, hτ₀⟩ := hne
  obtain ⟨h0₀, hones₀, -⟩ := hmemT τ₀ hτ₀
  have hL'1 : 1 ≤ L - Lp q := hones₀ ▸ E_ones_pos τ₀ (by omega) h0₀ _ (by omega)
  have hL't : L - Lp q ≤ s - P := hones₀ ▸ E_ones_le τ₀ _
  -- `N = t − 1`, `k = L' − 1`, `ρ̄ = k/N`
  obtain ⟨N, hN⟩ : ∃ N, N = s - P - 1 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = L - Lp q - 1 := ⟨_, rfl⟩
  have hkN : k ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hρ : rhoBar q s L P = (k : ℝ) / N := by
    unfold rhoBar; rw [← hN, ← hk]
  set ρ := rhoBar q s L P with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hNpos]; exact_mod_cast hkN
  -- window: the blocks `k₀, …, k₀ + m − 1`
  set m := (d - 1) / 2 with hm
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ = (s - P - d + 2) / 2 := ⟨_, rfl⟩
  have hk₀1 : 1 ≤ k₀ := by omega
  have hwin : 2 * k₀ - 1 + 2 * m ≤ s - P := by omega
  have hwd : s - P ≤ 2 * k₀ - 1 + d := by omega
  -- weights of the independent-letter model (position 0 fixed to 1)
  set p : ℕ → ℝ := fun i => if i = 0 then 1 else ρ with hpdef
  have hp01 : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i; simp only [hpdef]; split_ifs <;> constructor <;> linarith
  have hpρ : ∀ i, 2 * k₀ - 1 ≤ i → i < 2 * k₀ - 1 + 2 * m → p i = ρ := by
    intro i hi _; simp only [hpdef]; rw [if_neg (by omega)]
  have hGL := E_GL γ ρ hγ1 hγ2 hρ0 hρ1 (2 * k₀ - 1) m (s - P) (hp q P) p hp01 hpρ hwin
  -- the weight of an element of `𝒯` is `π = ρ̄^k (1 − ρ̄)^{N−k}`
  set π := ρ ^ k * (1 - ρ) ^ (N - k) with hπ
  have hνT : ∀ τ ∈ Tset q s L P, E_nu p τ = π := by
    intro τ hτ
    obtain ⟨h0, hones, -⟩ := hmemT τ hτ
    rw [hpdef, E_nu_tau ρ τ (by omega) h0, hones, hπ]
    rw [show L - Lp q - 1 = k by omega, show s - P - (L - Lp q) = N - k by omega]
  have hπ0 : 0 ≤ π := by rw [hπ]; exact mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg (by linarith) _)
  -- steps 2 and 3: `π Σ_{τ∈𝒯} γ^{N_d(τ)} ≤ Θ^m`
  set S := ∑ τ ∈ Tset q s L P, γ ^ (Nd q s P τ d) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun τ _ => pow_nonneg hγ0 _)
  have hπS : π * S ≤ Theta γ ρ ^ m := by
    calc π * S = ∑ τ ∈ Tset q s L P, E_nu p τ * γ ^ (Nd q s P τ d) := by
          rw [hS, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun τ hτ => by rw [hνT τ hτ])
      _ ≤ ∑ τ ∈ Tset q s L P, E_nu p τ * E_W γ (hp q P) τ (2 * k₀ - 1) m := by
          refine Finset.sum_le_sum (fun τ hτ => mul_le_mul_of_nonneg_left ?_ (E_nu_nonneg p hp01 τ))
          exact E_W_ge q s P γ hγ0 hγ2 τ (hmemT τ hτ).2.2 d k₀ m hk₀1 hwin hwd
      _ ≤ ∑ τ : Fin (s - P) → Bool, E_nu p τ * E_W γ (hp q P) τ (2 * k₀ - 1) m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun τ _ _ =>
            mul_nonneg (E_nu_nonneg p hp01 τ) (E_W_nonneg γ _ hγ0 τ _ _))
      _ ≤ Theta γ ρ ^ m := hGL
  -- step 4: the mode and Lemma 2.5 (iii)
  have hmode := E_mode N k hN1 hkN
  rw [← hρ] at hmode
  have hTl := T_lower q s L P (by omega) hL0 ⟨τ₀, hτ₀⟩
  rw [← hN, ← hk] at hTl
  have hTpos : (0 : ℝ) < (Tset q s L P).card := by
    exact_mod_cast Finset.card_pos.2 ⟨τ₀, hτ₀⟩
  have hC : (N.choose k : ℝ) ≤ N * (Tset q s L P).card := by
    rw [div_le_iff₀ hNpos] at hTl; linarith
  have hΘ := pow_nonneg (E_Theta_nonneg γ ρ hγ1 hγ2) m
  have htN : ((s - P : ℕ) : ℝ) = (N : ℝ) + 1 := by
    rw [hN]; push_cast [show 1 ≤ s - P by omega]; ring
  rw [← hN, htN]
  unfold ETail
  rw [← hS, div_le_iff₀ hTpos]
  calc S ≤ S * (((N : ℝ) + 1) * (N.choose k : ℝ) * π) := by
        rw [hπ, ← mul_assoc]; nlinarith
    _ = ((N : ℝ) + 1) * (N.choose k : ℝ) * (π * S) := by ring
    _ ≤ ((N : ℝ) + 1) * (N.choose k : ℝ) * Theta γ ρ ^ m := by
        apply mul_le_mul_of_nonneg_left hπS; positivity
    _ ≤ ((N : ℝ) + 1) * (N * (Tset q s L P).card) * Theta γ ρ ^ m := by
        apply mul_le_mul_of_nonneg_right _ hΘ
        exact mul_le_mul_of_nonneg_left hC (by positivity)
    _ = ((N : ℝ) + 1) * N * Theta γ ρ ^ m * (Tset q s L P).card := by ring

/-- General form of Lemma 6.4: if `s > q + 1` and `(L, P) ∈ RdeltaG a b δ` (`δ ≥ 0`, `bδ ≤ a`), then
`|ρ̄ − ρ_c| ≤ (aδq + a_λ)/(λ(s − q − 1))` (`a_λ = λ − 1`) and `t ≥ s − q + 1`. Version 3 has `(a, b) = (1.38, 4.48)` (§4.2.3 of version 3 of the manuscript). -/
theorem rhoBar_closeG (a b δ : ℝ) (s q L P : ℕ) (hδ : 0 ≤ δ) (hba : b * δ ≤ a) (hsq : q + 1 < s)
    (hR : RdeltaG a b δ s q L P) :
    |rhoBar q s L P - rhoc| ≤ (a * δ * q + aa) / (lam * (s - q - 1)) ∧ s - q + 1 ≤ s - P := by
  obtain ⟨hL0, hL1, hp0, hp1, _hPne, hTne, hPs⟩ := hR
  have hlam1 := E_lam_gt_one
  have ha := E_aa_pos
  have hLpq := E_lam_Lp_le q
  have hPq : P < q := by
    have : (P:ℝ) < q := by unfold hp at hp0; linarith
    exact_mod_cast this
  refine ⟨?_, by omega⟩
  obtain ⟨τ, hτ⟩ := hTne
  have ht0 : 0 < s - P := by omega
  have hL' : 1 ≤ L - Lp q := by
    classical
    simp only [Tset, Finset.mem_filter] at hτ
    obtain ⟨-, h0, hones, -⟩ := hτ
    rw [← hones]
    exact E_ones_pos τ ht0 (h0 ht0) _ (by omega)
  unfold rhoBar
  rw [Nat.cast_sub (by omega : 1 ≤ L - Lp q), Nat.cast_sub (by omega : Lp q ≤ L),
    Nat.cast_sub (by omega : 1 ≤ s - P), Nat.cast_sub (by omega : P ≤ s), Nat.cast_one]
  have hsP : (0:ℝ) < (s:ℝ) - P - 1 := by
    have : P + 1 < s := by omega
    have : ((P + 1 : ℕ) : ℝ) < s := by exact_mod_cast this
    push_cast at this; linarith
  have hsq' : (0:ℝ) < (s:ℝ) - q - 1 := by
    have : ((q + 1 : ℕ) : ℝ) < s := by exact_mod_cast hsq
    push_cast at this; linarith
  have hPq' : (P:ℝ) < q := by exact_mod_cast hPq
  have hlpos : 0 < lam := by linarith
  have hid : ((L:ℝ) - Lp q - 1) / ((s:ℝ) - P - 1) - rhoc =
      (hL s L - hp q P - aa) / (lam * ((s:ℝ) - P - 1)) := by
    unfold hL hp aa rhoc
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hlpos hsP)]
  have hnum : |hL s L - hp q P - aa| ≤ a * δ * q + aa := by
    have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
    have h35 : b * δ ^ 2 * q ≤ a * δ * q := by
      have e : b * δ ^ 2 * q = (b * δ) * (δ * q) := by ring
      have e2 : a * δ * q = a * (δ * q) := by ring
      rw [e, e2]; exact mul_le_mul_of_nonneg_right hba (mul_nonneg hδ hq0)
    rw [abs_le]; constructor <;> linarith
  have hnum0 : 0 ≤ a * δ * q + aa := by linarith
  calc |hL s L - hp q P - aa| / (lam * ((s:ℝ) - P - 1))
      ≤ (a * δ * q + aa) / (lam * ((s:ℝ) - P - 1)) := by
        gcongr
    _ ≤ (a * δ * q + aa) / (lam * ((s:ℝ) - q - 1)) := by
        apply div_le_div_of_nonneg_left hnum0 (mul_pos hlpos hsq')
        apply mul_le_mul_of_nonneg_left _ hlpos.le
        linarith

/-- Lemma 6.4: if `s > q + 1` and `(L, P) ∈ R_δ` (`δ ≤ 10^{−3}`), then `|ρ̄ − ρ_c| ≤ (1.23δq + a)/(λ(s − q − 1))` and `t ≥ s − q + 1`. -/
theorem rhoBar_close (δ : ℝ) (s q L P : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) (hsq : q + 1 < s)
    (hR : Rdelta δ s q L P) :
    |rhoBar q s L P - rhoc| ≤ (1.23 * δ * q + aa) / (lam * (s - q - 1)) ∧ s - q + 1 ≤ s - P :=
  rhoBar_closeG 1.23 3.5 δ s q L P hδ.le (by linarith) hsq hR

-- The hypotheses `hε`, `h1` are not needed in the proof (the statement is kept as in the skeleton).
set_option linter.unusedVariables false in
/-- `Θ_γ(ρ)` is increasing for `ρ ∈ [1/2, 1]`; if `|ρ − ρ_c| ≤ ε` (with `ρ_c + ε ≤ 1`), then `Θ_γ(ρ) ≤ Θ_γ(ρ_c + ε)` (for `γ ≤ 1`). -/
theorem Theta_le_of_close (γ ρ ε : ℝ) (hγ : γ ≤ 1) (hε : 0 ≤ ε) (h1 : rhoc + ε ≤ 1)
    (hρ : |ρ - rhoc| ≤ ε) : Theta γ ρ ≤ Theta γ (rhoc + ε) := by
  -- `hε`, `h1` are not used (`ρ_c > 1/2` suffices)
  have hc := E_rhoc_gt_half
  obtain ⟨hlo, hhi⟩ := abs_le.1 hρ
  unfold Theta
  have key : 0 ≤ (1 - γ) * ((rhoc + ε - ρ) * (ρ + (rhoc + ε) - 1)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  nlinarith [key]

end Collatz.M1
