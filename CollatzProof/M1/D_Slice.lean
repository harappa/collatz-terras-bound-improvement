import CollatzProof.M1.D_Word
import CollatzProof.M1.D_Fourier
import CollatzProof.M1.D_Orbit

/-!
# Auxiliary results for Theorem B: components on a slice

Lemma 3.3 (the form and range of `G` modulo `3^L`), Lemma 5.3 (the swap preserves `𝒯` and `ℬ` and shifts `G` by `D_k`;
the phase is `θ_b(N)`), and the form of Lemma 5.3 (iii), `|S(η_N)|² ≤ |𝒯| Σ_τ Π_{b∈ℬ(τ)} cos² πθ_b(N)`.
The prefix `D_` marks auxiliary declarations for Theorem B.
-/

namespace Collatz.M1

open Finset

/-! ## Auxiliary results on `ZMod` and additive characters -/

lemma D_isUnit_two (n : ℕ) : IsUnit (2 : ZMod (3 ^ n)) := by
  have h := (ZMod.isUnit_iff_coprime 2 (3 ^ n)).mpr (Nat.Coprime.pow_right n (by norm_num))
  exact_mod_cast h

/-- Defining property of `inv2mod`: `3^n ∣ ⟨2^{−k}a⟩_{3^n} 2^k − a`. -/
lemma D_inv2mod_spec (k n : ℕ) (a : ℤ) : (3 ^ n : ℤ) ∣ (inv2mod k n a : ℤ) * 2 ^ k - a := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((inv2mod k n a : ℤ) * 2 ^ k - a) (3 ^ n)).mp ?_
  · exact_mod_cast h
  · push_cast
    unfold inv2mod
    rw [ZMod.natCast_zmod_val, mul_assoc, ZMod.inv_mul_of_unit _ ((D_isUnit_two n).pow k), mul_one,
      sub_self]

lemma D_inv2mod_lt (k n : ℕ) (a : ℤ) : inv2mod k n a < 3 ^ n := by
  unfold inv2mod; exact ZMod.val_lt _

lemma D_three_pow_eq_zero (L : ℕ) : (3 : ZMod (3 ^ L)) ^ L = 0 := by
  exact_mod_cast ZMod.natCast_self (3 ^ L)

lemma D_psi_norm (M : ℕ) [NeZero M] (x : ZMod M) : ‖ZMod.stdAddChar x‖ = 1 := by
  have : x = ((x.val : ℤ) : ZMod M) := by simp
  rw [this, D_psi_int, D_norm_eC]

lemma D_psi_sum {ι : Type*} (M : ℕ) [NeZero M] (s : Finset ι) (g : ι → ZMod M) :
    ZMod.stdAddChar (∑ i ∈ s, g i) = ∏ i ∈ s, ZMod.stdAddChar (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-! ## Tail sets and swap blocks -/

section Slice

variable {q s L P : ℕ}

lemma D_mem_Tset {τ : Fin (s - P) → Bool} : τ ∈ Tset q s L P ↔
    ((∀ h : 0 < s - P, τ ⟨0, h⟩ = true) ∧ ones τ (s - P) = L - Lp q ∧ SurvW (hp q P) τ) := by
  classical
  unfold Tset; simp only [mem_filter, mem_univ, true_and]

lemma D_mem_Bset {τ : Fin (s - P) → Bool} {k : ℕ} : k ∈ Bset q s P τ ↔ IsSwap q s P τ k := by
  classical
  unfold Bset; simp only [mem_filter, mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨h1, _⟩ := h; omega

lemma D_IsSwap_iff {τ : Fin (s - P) → Bool} {k : ℕ} : IsSwap q s P τ k ↔
    (1 ≤ k ∧ 2 * k < s - P ∧ D_xb τ (2 * k - 1) ≠ D_xb τ (2 * k) ∧
      1 ≤ hw (hp q P) τ (2 * k - 1)) := by
  unfold IsSwap
  constructor
  · rintro ⟨h, h1, h2, h3⟩
    refine ⟨h1, h, ?_, h3⟩
    rw [D_xb_lt τ (by omega), D_xb_lt τ h]; exact h2
  · rintro ⟨h1, h, h2, h3⟩
    refine ⟨h, h1, ?_, h3⟩
    rw [D_xb_lt τ (by omega), D_xb_lt τ h] at h2; exact h2

lemma D_GoodU_of_sub {τ : Fin (s - P) → Bool} {U : Finset ℕ} (hU : U ⊆ Bset q s P τ) :
    D_GoodU U τ := by
  intro k hk
  obtain ⟨h1, h2, h3, _⟩ := D_IsSwap_iff.mp (D_mem_Bset.mp (hU hk))
  exact ⟨h1, h2, h3⟩

lemma D_Bset_sub (τ : Fin (s - P) → Bool) : Bset q s P τ ⊆ range (s - P) := by
  intro k hk
  obtain ⟨_, h2, _, _⟩ := D_IsSwap_iff.mp (D_mem_Bset.mp hk)
  rw [mem_range]; omega

lemma D_flip_block_ne {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (k : ℕ) (hk1 : 1 ≤ k)
    (hk2 : 2 * k < t) : (D_xb (D_flipU U τ) (2 * k - 1) ≠ D_xb (D_flipU U τ) (2 * k)) ↔
      (D_xb τ (2 * k - 1) ≠ D_xb τ (2 * k)) := by
  have e1 : (2 * k - 1 + 1) / 2 = k := by omega
  have e2 : (2 * k + 1) / 2 = k := by omega
  by_cases hkU : k ∈ U
  · rw [D_xb_flip_in U τ (by omega) ⟨by omega, by rw [e1]; exact hkU⟩,
      D_xb_flip_in U τ hk2 ⟨by omega, by rw [e2]; exact hkU⟩]
    cases D_xb τ (2 * k - 1) <;> cases D_xb τ (2 * k) <;> simp
  · rw [D_xb_flip_out U τ (by rw [e1]; tauto), D_xb_flip_out U τ (by rw [e2]; tauto)]

/-- Lemma 5.3 (i): the swap preserves `ℬ`. -/
lemma D_flip_Bset {τ : Fin (s - P) → Bool} {U : Finset ℕ} (hU : U ⊆ Bset q s P τ) :
    Bset q s P (D_flipU U τ) = Bset q s P τ := by
  have hG := D_GoodU_of_sub hU
  ext k
  rw [D_mem_Bset, D_mem_Bset, D_IsSwap_iff, D_IsSwap_iff]
  have hhw : hw (hp q P) (D_flipU U τ) (2 * k - 1) = hw (hp q P) τ (2 * k - 1) := by
    unfold hw; rw [D_ones_flip_blockstart U τ hG k]
  rw [hhw]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (D_flip_block_ne U τ k h1 h2).mp h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (D_flip_block_ne U τ k h1 h2).mpr h3, h4⟩

lemma D_lam_pos : 0 < lam := by have := lam_bounds; linarith [this.1]

/-- Lemma 5.3 (i): the swap preserves `𝒯`. -/
lemma D_flip_Tset {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) {U : Finset ℕ}
    (hU : U ⊆ Bset q s P τ) : D_flipU U τ ∈ Tset q s L P := by
  have hG := D_GoodU_of_sub hU
  obtain ⟨h0, h1, h2⟩ := D_mem_Tset.mp hτ
  refine D_mem_Tset.mpr ⟨?_, ?_, ?_⟩
  · intro h; simpa [D_flipU] using h0 h
  · rw [D_ones_flip_total U τ hG]; exact h1
  · intro j hj1 hj2
    by_cases hj : j % 2 = 0 ∧ j / 2 ∈ U
    · obtain ⟨hk1, _, _, hk4⟩ := D_IsSwap_iff.mp (D_mem_Bset.mp (hU hj.2))
      have hj' : j = 2 * (j / 2) := by omega
      have hge : ones τ (2 * (j / 2) - 1) ≤ ones (D_flipU U τ) j := by
        rw [← D_ones_flip_blockstart U τ hG (j / 2)]; exact D_ones_mono _ (by omega)
      unfold hw at hk4 ⊢
      have hge' : (ones τ (2 * (j / 2) - 1) : ℝ) ≤ ones (D_flipU U τ) j := by exact_mod_cast hge
      have hcast : ((2 * (j / 2) - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), ← hj']; push_cast; ring
      rw [hcast] at hk4
      have := D_lam_pos
      nlinarith
    · have := D_ones_flip_eq U τ hG j hj
      unfold hw; rw [this]; exact h2 j hj1 hj2

/-! ## Lemma 3.3: the form and range of `G` modulo `3^L` -/

/-- Lemma 3.3 (i): `G(τ) 2^t ≡ c_τ` (mod `3^L`). -/
lemma D_G_mul {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (hLp : Lp q ≤ L) :
    ((Gstat q s L P τ : ℤ) : ZMod (3 ^ L)) * 2 ^ (s - P) = (cOf τ : ZMod (3 ^ L)) := by
  obtain ⟨_, h1, _⟩ := D_mem_Tset.mp hτ
  have hdual := dual_word τ
  rw [h1] at hdual
  obtain ⟨c, hc⟩ := D_inv2mod_spec (s - P) (Lp q) (mOf τ)
  have hd : (2 : ℤ) ^ (s - P) * aOf τ = 3 ^ (L - Lp q) * mOf τ + cOf τ := by exact_mod_cast hdual
  have hLL : (3 : ℤ) ^ L = 3 ^ (L - Lp q) * 3 ^ Lp q := by rw [← pow_add]; congr 1; omega
  have key : (Gstat q s L P τ : ℤ) * 2 ^ (s - P) - cOf τ = -(3 ^ L * c) := by
    unfold Gstat
    linear_combination hd - 3 ^ (L - Lp q) * hc + c * hLL
  have key2 := congrArg (fun x : ℤ => (x : ZMod (3 ^ L))) key
  push_cast at key2
  rw [D_three_pow_eq_zero, zero_mul, neg_zero, sub_eq_zero] at key2
  exact key2

lemma D_mOf_pos {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (ht : 0 < s - P) : 0 < mOf τ := by
  obtain ⟨h0, _, _⟩ := D_mem_Tset.mp hτ
  have := (D_parity_mOf τ (i := 0) ht).mpr (by rw [D_xb_lt τ ht]; exact h0 ht)
  simp at this; omega

/-- Lemma 3.3 (ii): if `2^t < 3^{L_p}` then `−3^L < G(τ) < 0`. -/
lemma D_G_range {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (hLp : Lp q ≤ L) (ht : 0 < s - P)
    (h2t : 2 ^ (s - P) < 3 ^ Lp q) :
    -(3 ^ L : ℤ) < Gstat q s L P τ ∧ Gstat q s L P τ < 0 := by
  obtain ⟨_, h1, _⟩ := D_mem_Tset.mp hτ
  have ha := aOf_lt τ
  rw [h1] at ha
  have hm := D_mOf_pos hτ ht
  have hm2 := mOf_lt τ
  set y := inv2mod (s - P) (Lp q) (mOf τ) with hy
  have hylt : y < 3 ^ Lp q := D_inv2mod_lt _ _ _
  have hy1 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · exfalso
      obtain ⟨c, hc⟩ := D_inv2mod_spec (s - P) (Lp q) (mOf τ)
      rw [← hy, h] at hc
      simp only [Nat.cast_zero, zero_mul, zero_sub] at hc
      -- `3^{L_p} ∣ m`, but `0 < m < 3^{L_p}`
      have hm' : (mOf τ : ℤ) = -(3 ^ Lp q * c) := by linarith
      have hc0 : c < 0 := by
        rcases lt_or_ge c 0 with hc0 | hc0
        · exact hc0
        · have : (0 : ℤ) < mOf τ := by exact_mod_cast hm
          nlinarith [pow_pos (show (0:ℤ) < 3 by norm_num) (Lp q)]
      have : (3 : ℤ) ^ Lp q ≤ mOf τ := by
        rw [hm']; nlinarith [pow_pos (show (0:ℤ) < 3 by norm_num) (Lp q)]
      have : (mOf τ : ℤ) < 3 ^ Lp q := by exact_mod_cast lt_trans hm2 h2t
      linarith
    · exact h
  have hLL : (3 : ℤ) ^ L = 3 ^ (L - Lp q) * 3 ^ Lp q := by rw [← pow_add]; congr 1; omega
  unfold Gstat
  rw [← hy]
  have ha' : (aOf τ : ℤ) < 3 ^ (L - Lp q) := by exact_mod_cast ha
  have hy1' : (1 : ℤ) ≤ y := by exact_mod_cast hy1
  have hylt' : (y : ℤ) + 1 ≤ 3 ^ Lp q := by exact_mod_cast hylt
  have hp : (0 : ℤ) < 3 ^ (L - Lp q) := by positivity
  constructor
  · rw [hLL]; nlinarith [Int.natCast_nonneg (aOf τ)]
  · nlinarith

/-! ## Lemma 5.3 (ii): the change of `G` under the swap, and the phase -/

/-- The change of `G` under the swap, `D_k = ε_k 3^{L'−j_k} 2^{2k−1} 2^{−t}` (mod `3^L`). -/
noncomputable def D_Dk (L : ℕ) {t : ℕ} (τ : Fin t → Bool) (k : ℕ) : ZMod (3 ^ L) :=
  ((D_eps τ k * 3 ^ (ones τ t - (ones τ (2 * k - 1) + 1)) * 2 ^ (2 * k - 1) : ℤ) : ZMod (3 ^ L)) *
    ((2 : ZMod (3 ^ L)) ^ t)⁻¹

/-- `G(flip_U τ) = G(τ) + Σ_{k∈U} D_k` (mod `3^L`). -/
lemma D_G_flip {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (hLp : Lp q ≤ L) {U : Finset ℕ}
    (hU : U ⊆ Bset q s P τ) :
    ((Gstat q s L P (D_flipU U τ) : ℤ) : ZMod (3 ^ L)) =
      ((Gstat q s L P τ : ℤ) : ZMod (3 ^ L)) + ∑ k ∈ U, D_Dk L τ k := by
  have h1 := D_G_mul (D_flip_Tset hτ hU) hLp
  have h2 := D_G_mul hτ hLp
  have hc := D_cw_flipU τ U (D_GoodU_of_sub hU)
  rw [D_cOf_eq] at h1 h2
  have hc' := congrArg (fun x : ℤ => (x : ZMod (3 ^ L))) hc
  push_cast at hc'
  have hu : ((2 : ZMod (3 ^ L)) ^ (s - P)) * ((2 : ZMod (3 ^ L)) ^ (s - P))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((D_isUnit_two L).pow _)
  unfold D_Dk
  push_cast
  rw [← sum_mul]
  set u := (2 : ZMod (3 ^ L)) ^ (s - P)
  set G' := ((Gstat q s L P (D_flipU U τ) : ℤ) : ZMod (3 ^ L))
  set G := ((Gstat q s L P τ : ℤ) : ZMod (3 ^ L))
  calc G' = G' * u * u⁻¹ := by rw [mul_assoc, hu, mul_one]
    _ = _ := by rw [h1, hc', ← h2]; linear_combination G * hu

lemma D_ones_block_le {τ : Fin (s - P) → Bool} {k : ℕ} (hk : k ∈ Bset q s P τ) :
    ones τ (2 * k - 1) + 1 ≤ ones τ (s - P) := by
  obtain ⟨hk1, hk2, hk3, _⟩ := D_IsSwap_iff.mp (D_mem_Bset.mp hk)
  have e1 := D_ones_succ τ (2 * k - 1)
  have e2 := D_ones_succ τ (2 * k)
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at e1
  have hm := D_ones_mono τ (show 2 * k + 1 ≤ s - P by omega)
  revert hk3 e1 e2
  cases D_xb τ (2 * k - 1) <;> cases D_xb τ (2 * k) <;> simp <;> omega

/-- Lemma 5.3 (ii): if `η_N = −2^{−q}N`, then `|(1 + ψ(η D_k))/2|² = cos² πθ_k(N)`. -/
lemma D_phase {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (hLp : Lp q ≤ L) {k : ℕ}
    (hk : k ∈ Bset q s P τ) (N : ℤ) (η : ZMod (3 ^ L))
    (hN : ((N : ℤ) : ZMod (3 ^ L)) = -(η * 2 ^ q)) :
    ‖(1 + ZMod.stdAddChar (η * D_Dk L τ k)) / 2‖ ^ 2 =
      Real.cos (Real.pi * theta q s P τ k N) ^ 2 := by
  obtain ⟨hk1, hk2, _, _⟩ := D_IsSwap_iff.mp (D_mem_Bset.mp hk)
  obtain ⟨_, hL', _⟩ := D_mem_Tset.mp hτ
  have hj := D_ones_block_le hk
  set o := ones τ (2 * k - 1) with ho
  set L' := ones τ (s - P) with hL'def
  set n := Lp q + (o + 1) with hn
  set e := L' - (o + 1) with he
  set d := (s - P) - (2 * k - 1) with hd
  have hLne : L = n + e := by omega
  set x := inv2mod (d + q) n (-N) with hx
  obtain ⟨c, hc⟩ := D_inv2mod_spec (d + q) n (-N)
  rw [← hx] at hc
  -- `3^L ∣ 3^e (x 2^{d+q} + N)`
  have h3 : (((x : ℤ) * 2 ^ (d + q) + N) * 3 ^ e : ℤ) = 3 ^ L * c := by
    rw [hLne, pow_add]; linear_combination (3 ^ e : ℤ) * hc
  have h3' := congrArg (fun y : ℤ => (y : ZMod (3 ^ L))) h3
  push_cast at h3'
  rw [D_three_pow_eq_zero, zero_mul] at h3'
  -- Claim: `η D_k = ε 3^e x` (mod `3^L`)
  have hu : ∀ m : ℕ, IsUnit ((2 : ZMod (3 ^ L)) ^ m) := fun m => (D_isUnit_two L).pow m
  have hinv : ((2 : ZMod (3 ^ L)) ^ (s - P)) * ((2 : ZMod (3 ^ L)) ^ (s - P))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (hu (s - P))
  have hpow : (2 : ZMod (3 ^ L)) ^ (s - P) * 2 ^ q = 2 ^ (d + q) * 2 ^ (2 * k - 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have claim : η * D_Dk L τ k = ((D_eps τ k * 3 ^ e * x : ℤ) : ZMod (3 ^ L)) := by
    rw [← (hu (s - P + q)).mul_left_inj]
    unfold D_Dk
    rw [← ho, ← hL'def, ← he]
    push_cast
    rw [pow_add]
    linear_combination (η * (D_eps τ k : ZMod (3 ^ L)) * 3 ^ e * 2 ^ (2 * k - 1) * 2 ^ q) * hinv -
      ((D_eps τ k : ZMod (3 ^ L)) * 3 ^ e * x) * hpow +
      ((D_eps τ k : ZMod (3 ^ L)) * 3 ^ e * 2 ^ (2 * k - 1)) * hN -
      ((D_eps τ k : ZMod (3 ^ L)) * 2 ^ (2 * k - 1)) * h3'
  rw [claim, D_psi_int, D_norm_one_add_eC_sq]
  unfold theta
  have hnb : nb q s P τ k = n := rfl
  have hdb : db s P k = d := rfl
  rw [hnb, hdb, ← hx]
  have hval : Real.pi * ((((D_eps τ k * 3 ^ e * x : ℤ) : ℝ)) / ((3 ^ L : ℕ) : ℝ)) =
      (D_eps τ k : ℝ) * (Real.pi * ((x : ℝ) / 3 ^ n)) := by
    rw [hLne]; push_cast; rw [pow_add]; field_simp
  rw [hval]
  unfold D_eps
  split_ifs
  · simp
  · simp [neg_mul, Real.cos_neg]

/-- Lemma 5.3 (iii): `|S(η)|² ≤ |𝒯| Σ_τ Π_{b∈ℬ(τ)} cos² πθ_b(N)` (`η = −2^{−q}N`). -/
lemma D_S_bound (hLp : Lp q ≤ L) (N : ℤ) (η : ZMod (3 ^ L))
    (hN : ((N : ℤ) : ZMod (3 ^ L)) = -(η * 2 ^ q)) :
    ‖∑ τ ∈ Tset q s L P, ZMod.stdAddChar (η * ((Gstat q s L P τ : ℤ) : ZMod (3 ^ L)))‖ ^ 2 ≤
      (Tset q s L P).card * ∑ τ ∈ Tset q s L P, riesz q s P τ N := by
  refine (D_orbit_bound (Tset q s L P) (Bset q s P) (range (s - P)) D_flipU
    (fun τ _ => D_Bset_sub τ) (fun τ hτ U hU => D_flip_Tset hτ hU) (fun τ _ U hU => D_flip_Bset hU)
    (fun τ _ U _ => D_flipU_invol U τ)
    (fun τ => ZMod.stdAddChar (η * ((Gstat q s L P τ : ℤ) : ZMod (3 ^ L))))
    (fun τ k => ZMod.stdAddChar (η * D_Dk L τ k)) ?_ ?_).trans ?_
  · intro τ hτ U hU
    beta_reduce  -- in v4.30 the goal left by `refine` is not β-reduced
    rw [D_G_flip hτ hLp hU, mul_add, AddChar.map_add_eq_mul, mul_sum, D_psi_sum]
  · intro τ _; exact D_psi_norm _ _
  · apply le_of_eq
    congr 1
    apply sum_congr rfl
    intro τ hτ
    unfold riesz
    apply prod_congr rfl
    intro k hk
    exact D_phase hτ hLp hk N η hN

end Slice

end Collatz.M1
