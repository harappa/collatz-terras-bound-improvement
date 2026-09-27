import CollatzProof.M1.D_CRT

/-!
# Auxiliary results for Theorem B: Lemma 5.5 (reduction)

`Σ_{ξ≠0} |Ê(ξ)|²|Ĝ(ξ)|² ≤ 4(L+1)² W |𝒯|² B` (with `A_k ≤ B` on every shell).
Instead of the manuscript's `Γ_L = 3 + L ln 3`, we use `Σ_η |ω_ξ(η)| ≤ Σ_k bnd_k · #(residue classes of J_k) ≤ 2(L+1)` (the same in the qualitative form).
The prefix `D_` marks auxiliary declarations for Theorem B.
-/

namespace Collatz.M1

open Finset

section CRT2

variable (q L : ℕ)

lemma D_Nrep_modQ (ξ : ℕ) (η : ZMod (3 ^ L)) :
    ((D_Nrep q L ξ η : ℤ) : ZMod (2 ^ q)) = (ξ : ZMod (2 ^ q)) * 3 ^ L := by
  obtain ⟨m, hm⟩ := D_Nrep_cong q L ξ η
  have h := congrArg (fun x : ℤ => (x : ZMod (2 ^ q))) hm
  push_cast at h
  have e2 : (2 : ZMod (2 ^ q)) ^ q = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ q)
  rw [e2] at h
  linear_combination -h

/-- At most one element of `[0, 2^q)` lies in the residue class `r`. -/
lemma D_count_range_le (r : ZMod (2 ^ q)) :
    ∑ i ∈ range (2 ^ q), (if ((i : ℤ) : ZMod (2 ^ q)) = r then (1 : ℝ) else 0) ≤ 1 := by
  classical
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have : ((range (2 ^ q)).filter (fun i : ℕ => ((i : ℤ) : ZMod (2 ^ q)) = r)).card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_filter, mem_range, Int.cast_natCast] at ha hb
    have := ha.2.trans hb.2.symm
    have h1 := congrArg ZMod.val this
    rwa [ZMod.val_cast_of_lt ha.1, ZMod.val_cast_of_lt hb.1] at h1
  exact_mod_cast this

/-- `ℓ^1` estimate: `Σ_η |ω_ξ(η)| ≤ 2(L+1)`. -/
lemma D_omega_l1 (hq : 1 ≤ q) {ξ : ℕ} (hξ : ξ < 2 ^ q) :
    ∑ η : ZMod (3 ^ L), ‖D_omega q L ξ η‖ ≤ 2 * (L + 1) := by
  classical
  have hω : ∀ η : ZMod (3 ^ L), ‖D_omega q L ξ η‖ ≤
      ∑ k ∈ range (L + 1), (if D_Nrep q L ξ η ∈ shell q k then D_bnd k else 0) := by
    intro η
    obtain ⟨m, hm⟩ := D_Nrep_cong q L ξ η
    rw [D_omega_eq q L ξ η _ m (by exact_mod_cast hm)]
    obtain ⟨hb1, hb2⟩ := D_Nrep_bounds q L hq ξ η
    obtain ⟨k, hk, hN⟩ := D_shell_cover q L _ hb1 hb2
    calc ‖D_om q L (D_Nrep q L ξ η)‖ ≤ D_bnd k := D_norm_om_shell q L k hq hk _ hN
      _ = (if D_Nrep q L ξ η ∈ shell q k then D_bnd k else 0) := by rw [if_pos hN]
      -- In v4.30 the goal of the hypothesis of `single_le_sum` is left without β-reduction, so we `beta_reduce` before the case split
      _ ≤ _ := single_le_sum (f := fun k => if D_Nrep q L ξ η ∈ shell q k then D_bnd k else 0)
          (fun k _ => by beta_reduce; split_ifs; exact D_bnd_nonneg k; exact le_rfl)
          (mem_range.mpr (by omega))
  have hcount : ∀ k, ((univ.filter (fun η : ZMod (3 ^ L) => D_Nrep q L ξ η ∈ shell q k)).card : ℝ) ≤
      D_shc k := by
    intro k
    set r : ZMod (2 ^ q) := (ξ : ZMod (2 ^ q)) * 3 ^ L
    have h1 : (univ.filter (fun η : ZMod (3 ^ L) => D_Nrep q L ξ η ∈ shell q k)).card ≤
        ((shell q k).filter (fun N => ((N : ℤ) : ZMod (2 ^ q)) = r)).card := by
      apply card_le_card_of_injOn (fun η => D_Nrep q L ξ η)
      · intro η hη
        have hη' : D_Nrep q L ξ η ∈ shell q k := (mem_filter.mp (mem_coe.mp hη)).2
        exact mem_coe.mpr (mem_filter.mpr ⟨hη', D_Nrep_modQ q L ξ η⟩)
      · intro η _ η' _ heq
        have := D_Nrep_inj q L (x₁ := (ξ, η)) (x₂ := (ξ, η'))
          (mem_coe.mpr (mem_product.mpr ⟨mem_range.mpr hξ, mem_univ _⟩))
          (mem_coe.mpr (mem_product.mpr ⟨mem_range.mpr hξ, mem_univ _⟩)) heq
        exact (Prod.mk.inj this).2
    have h2 : (((shell q k).filter (fun N => ((N : ℤ) : ZMod (2 ^ q)) = r)).card : ℝ) =
        ∑ N ∈ shell q k, (if ((N : ℤ) : ZMod (2 ^ q)) = r then (1 : ℝ) else 0) := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have h3 := D_shell_sum q hq (fun N => if ((N : ℤ) : ZMod (2 ^ q)) = r then (1 : ℝ) else 0)
      (by intro N; push_cast
          rw [show (2 : ZMod (2 ^ q)) ^ q = 0 by exact_mod_cast ZMod.natCast_self (2 ^ q), add_zero]) k
    have h4 := D_count_range_le q r
    have hshc : 0 ≤ D_shc k := by unfold D_shc; split_ifs <;> positivity
    calc ((univ.filter (fun η : ZMod (3 ^ L) => D_Nrep q L ξ η ∈ shell q k)).card : ℝ)
        ≤ (((shell q k).filter (fun N => ((N : ℤ) : ZMod (2 ^ q)) = r)).card : ℝ) := by
          exact_mod_cast h1
      _ = _ := h2
      _ = _ := h3
      _ ≤ D_shc k * 1 := by gcongr
      _ = D_shc k := mul_one _
  calc ∑ η : ZMod (3 ^ L), ‖D_omega q L ξ η‖
      ≤ ∑ η : ZMod (3 ^ L), ∑ k ∈ range (L + 1),
          (if D_Nrep q L ξ η ∈ shell q k then D_bnd k else 0) := sum_le_sum (fun η _ => hω η)
    _ = ∑ k ∈ range (L + 1), ∑ η : ZMod (3 ^ L),
          (if D_Nrep q L ξ η ∈ shell q k then D_bnd k else 0) := sum_comm
    _ = ∑ k ∈ range (L + 1), D_bnd k *
          ((univ.filter (fun η : ZMod (3 ^ L) => D_Nrep q L ξ η ∈ shell q k)).card : ℝ) := by
        apply sum_congr rfl; intro k _
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ range (L + 1), (2 : ℝ) := by
        apply sum_le_sum; intro k _
        exact (mul_le_mul_of_nonneg_left (hcount k) (D_bnd_nonneg k)).trans (D_bnd_shc k)
    _ = 2 * (L + 1) := by simp; ring

end CRT2

/-! ## The weight `w(N)` -/

section Weights

variable {q s L P : ℕ}

lemma D_wN_nonneg (N : ℤ) : 0 ≤ wN q s L N := by
  unfold wN; split_ifs <;> positivity

lemma D_wN_per (N : ℤ) : wN q s L (N + 2 ^ q) = wN q s L N := by
  unfold wN xiN
  have : (((N + 2 ^ q : ℤ)) : ZMod (2 ^ q)) = ((N : ℤ) : ZMod (2 ^ q)) := by
    push_cast
    rw [show (2 : ZMod (2 ^ q)) ^ q = 0 by exact_mod_cast ZMod.natCast_self (2 ^ q), add_zero]
  rw [this]

lemma D_xiN_inj {i i' : ℕ} (hi : i < 2 ^ q) (hi' : i' < 2 ^ q) (h : xiN q L i = xiN q L i') :
    i = i' := by
  unfold xiN at h
  have h1 := ZMod.val_injective _ h
  have hu := D_isUnit_three q L
  have h2 : ((i : ℤ) : ZMod (2 ^ q)) = ((i' : ℤ) : ZMod (2 ^ q)) := by
    have := congrArg (· * (3 : ZMod (2 ^ q)) ^ L) h1
    simp only [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one] at this
    exact this
  simp only [Int.cast_natCast] at h2
  have h3 := congrArg ZMod.val h2
  rwa [ZMod.val_cast_of_lt hi, ZMod.val_cast_of_lt hi'] at h3

lemma D_sum_wN_range : ∑ i ∈ range (2 ^ q), wN q s L (i : ℤ) ≤ Wsum q (Eset q (hL s L)) := by
  classical
  have e : ∑ i ∈ range (2 ^ q), wN q s L (i : ℤ) =
      ∑ i ∈ (range (2 ^ q)).filter (fun i : ℕ => xiN q L (i : ℤ) ≠ 0),
        ‖Ehat q (Eset q (hL s L)) (xiN q L (i : ℤ))‖ ^ 2 := by
    rw [sum_filter]
    apply sum_congr rfl; intro i _
    unfold wN; split_ifs <;> simp_all
  rw [e, ← sum_image (g := fun i : ℕ => xiN q L (i : ℤ))
    (f := fun ξ : ℕ => ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2)]
  · unfold Wsum
    apply sum_le_sum_of_subset_of_nonneg
    · intro ξ hξ
      rw [mem_image] at hξ
      obtain ⟨i, hi, rfl⟩ := hξ
      rw [mem_filter] at hi
      rw [mem_erase, mem_range]
      exact ⟨hi.2, by unfold xiN; exact ZMod.val_lt _⟩
    · intro _ _ _; positivity
  · intro i hi i' hi' h
    have h1 := (mem_filter.mp (mem_coe.mp hi)).1
    have h2 := (mem_filter.mp (mem_coe.mp hi')).1
    exact D_xiN_inj (mem_range.mp h1) (mem_range.mp h2) h

/-- `Σ_{N∈J_k} w(N) ≤ c_k W`. -/
lemma D_shell_w (hq : 1 ≤ q) (k : ℕ) :
    ∑ N ∈ shell q k, wN q s L N ≤ D_shc k * Wsum q (Eset q (hL s L)) := by
  rw [D_shell_sum q hq (wN q s L) D_wN_per k]
  have : 0 ≤ D_shc k := by unfold D_shc; split_ifs <;> positivity
  gcongr
  exact D_sum_wN_range

/-- `Σ_{N∈J_k} w(N) F(N) = (Σ_{N∈J_k} w(N)) ⟨F⟩_k`. -/
lemma D_shAvg_mul (k : ℕ) (F : ℤ → ℝ) :
    ∑ N ∈ shell q k, wN q s L N * F N = (∑ N ∈ shell q k, wN q s L N) * shAvg q s L k F := by
  unfold shAvg
  by_cases h : ∑ N ∈ shell q k, wN q s L N = 0
  · rw [h, zero_mul]
    have hz := (sum_eq_zero_iff_of_nonneg (fun N _ => D_wN_nonneg (q := q) (s := s) (L := L) N)).mp h
    exact sum_eq_zero (fun N hN => by rw [hz N hN, zero_mul])
  · field_simp

lemma D_riesz_nonneg (τ : Fin (s - P) → Bool) (N : ℤ) : 0 ≤ riesz q s P τ N := by
  unfold riesz; exact prod_nonneg (fun _ _ => sq_nonneg _)

end Weights

/-! ## Lemma 5.5 (reduction) -/

section Reduce

variable {q s L P : ℕ}

/-- Main part of Lemma 5.5: `Σ_{ξ≠0} Σ_η |Ê(ξ)|² |ω_ξ(η)| |S(η)|² ≤ 2(L+1) |𝒯|² W B`. -/
lemma D_main_sum (hq : 1 ≤ q) (hLp : Lp q ≤ L) (hTne : (Tset q s L P).Nonempty) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ k ≤ L, Ak q s L P k ≤ B) :
    ∑ ξ ∈ (range (2 ^ q)).erase 0, ∑ η : ZMod (3 ^ L),
        ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * (‖D_omega q L ξ η‖ * ‖D_S q s L P η‖ ^ 2) ≤
      2 * (L + 1) * ((Tset q s L P).card : ℝ) ^ 2 * Wsum q (Eset q (hL s L)) * B := by
  classical
  set T := Tset q s L P
  set W := Wsum q (Eset q (hL s L))
  set R : ℤ → ℝ := fun N => ∑ τ ∈ T, riesz q s P τ N with hR
  have hRn : ∀ N, 0 ≤ R N := fun N => sum_nonneg (fun τ _ => D_riesz_nonneg τ N)
  set g : ℤ → ℝ := fun N => wN q s L N * ((T.card : ℝ) * R N) with hg
  have hgn : ∀ N, 0 ≤ g N := fun N => mul_nonneg (D_wN_nonneg N) (mul_nonneg (by positivity) (hRn N))
  set Φ : ℤ → ℝ := fun N => ∑ k ∈ range (L + 1), if N ∈ shell q k then D_bnd k * g N else 0 with hΦ
  have hΦn : ∀ N, 0 ≤ Φ N := fun N => sum_nonneg (fun k _ => by
    split_ifs; exact mul_nonneg (D_bnd_nonneg k) (hgn N); exact le_rfl)
  -- 1. Estimate of each term
  have step1 : ∀ ξ ∈ (range (2 ^ q)).erase 0, ∀ η : ZMod (3 ^ L),
      ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * (‖D_omega q L ξ η‖ * ‖D_S q s L P η‖ ^ 2) ≤
        Φ (D_Nrep q L ξ η) := by
    intro ξ hξ η
    rw [mem_erase, mem_range] at hξ
    obtain ⟨m, hm⟩ := D_Nrep_cong q L ξ η
    obtain ⟨hb1, hb2⟩ := D_Nrep_bounds q L hq ξ η
    obtain ⟨k, hk, hN⟩ := D_shell_cover q L _ hb1 hb2
    set N := D_Nrep q L ξ η
    have hw : ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 = wN q s L N := by
      unfold wN; rw [D_xiN_Nrep q L hξ.2 η, if_neg hξ.1]
    have hom : ‖D_omega q L ξ η‖ ≤ D_bnd k := by
      rw [D_omega_eq q L ξ η _ m (by exact_mod_cast hm)]
      exact D_norm_om_shell q L k hq hk _ hN
    have hS : ‖D_S q s L P η‖ ^ 2 ≤ (T.card : ℝ) * R N :=
      D_S_bound hLp N η (D_Nrep_modM q L ξ η)
    calc ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * (‖D_omega q L ξ η‖ * ‖D_S q s L P η‖ ^ 2)
        ≤ wN q s L N * (D_bnd k * ((T.card : ℝ) * R N)) := by
          rw [hw]
          apply mul_le_mul_of_nonneg_left _ (D_wN_nonneg N)
          exact mul_le_mul hom hS (sq_nonneg _) (D_bnd_nonneg k)
      _ = (if N ∈ shell q k then D_bnd k * g N else 0) := by rw [if_pos hN, hg]; ring
      _ ≤ Φ N := single_le_sum (f := fun k => if N ∈ shell q k then D_bnd k * g N else 0)
          (fun k _ => by
            beta_reduce; split_ifs; exact mul_nonneg (D_bnd_nonneg k) (hgn N); exact le_rfl)
          (mem_range.mpr (by omega))
  -- 2. `(ξ, η) ↦ N` is injective
  set A := ((range (2 ^ q)).erase 0) ×ˢ (univ : Finset (ZMod (3 ^ L)))
  have hinj : Set.InjOn (fun p : ℕ × ZMod (3 ^ L) => D_Nrep q L p.1 p.2) (A : Set _) :=
    (D_Nrep_inj q L).mono (by
      intro p hp
      simp only [A, coe_product, Set.mem_prod, mem_coe, mem_erase, mem_range] at hp ⊢
      exact ⟨hp.1.2, hp.2⟩)
  have step2 : ∑ ξ ∈ (range (2 ^ q)).erase 0, ∑ η : ZMod (3 ^ L), Φ (D_Nrep q L ξ η) =
      ∑ N ∈ A.image (fun p => D_Nrep q L p.1 p.2), Φ N := by
    rw [sum_image hinj, sum_product]
  -- 3. Split by shells
  have step3 : ∀ k ∈ range (L + 1),
      ∑ N ∈ A.image (fun p => D_Nrep q L p.1 p.2), (if N ∈ shell q k then D_bnd k * g N else 0) ≤
        D_bnd k * ∑ N ∈ shell q k, g N := by
    intro k _
    rw [← sum_filter, ← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (D_bnd_nonneg k)
    apply sum_le_sum_of_subset_of_nonneg
    · intro N hN; exact (mem_filter.mp hN).2
    · intro N _ _; exact hgn N
  -- 4. Write the sum over a shell in terms of `A_k`
  have hTc : (T.card : ℝ) ≠ 0 := by exact_mod_cast hTne.card_pos.ne'
  have hW0 : 0 ≤ W := by
    simp only [W, Wsum]; exact sum_nonneg (fun _ _ => by positivity)
  have step4 : ∀ k ∈ range (L + 1), D_bnd k * ∑ N ∈ shell q k, g N ≤
      2 * ((T.card : ℝ) ^ 2 * W * B) := by
    intro k hk
    have hk' : k ≤ L := by rw [mem_range] at hk; omega
    set SW := ∑ N ∈ shell q k, wN q s L N
    have hSW0 : 0 ≤ SW := sum_nonneg (fun N _ => D_wN_nonneg N)
    have e1 : ∑ N ∈ shell q k, g N = (T.card : ℝ) ^ 2 * SW * Ak q s L P k := by
      have e2 : ∑ N ∈ shell q k, g N =
          (T.card : ℝ) * ∑ τ ∈ T, ∑ N ∈ shell q k, wN q s L N * riesz q s P τ N := by
        simp only [hg, hR, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro N _; apply sum_congr rfl; intro τ _; ring
      rw [e2, sum_congr rfl (fun τ _ => D_shAvg_mul (q := q) (s := s) (L := L) k (riesz q s P τ)),
        ← mul_sum]
      rw [show Ak q s L P k = (∑ τ ∈ T, shAvg q s L k (riesz q s P τ)) / T.card from rfl]
      field_simp
      rw [mul_comm]
    have hw := D_shell_w (s := s) (L := L) hq k
    have hbs := D_bnd_shc k
    have hb0 := D_bnd_nonneg k
    have hshc : 0 ≤ D_shc k := by unfold D_shc; split_ifs <;> positivity
    rw [e1]
    calc D_bnd k * ((T.card : ℝ) ^ 2 * SW * Ak q s L P k)
        ≤ D_bnd k * ((T.card : ℝ) ^ 2 * SW * B) := by
          apply mul_le_mul_of_nonneg_left _ hb0
          exact mul_le_mul_of_nonneg_left (hA k hk') (by positivity)
      _ ≤ D_bnd k * ((T.card : ℝ) ^ 2 * (D_shc k * W) * B) := by
          apply mul_le_mul_of_nonneg_left _ hb0
          apply mul_le_mul_of_nonneg_right _ hB
          exact mul_le_mul_of_nonneg_left hw (by positivity)
      _ = (D_bnd k * D_shc k) * ((T.card : ℝ) ^ 2 * W * B) := by ring
      _ ≤ 2 * ((T.card : ℝ) ^ 2 * W * B) :=
          mul_le_mul_of_nonneg_right hbs (by positivity)
  -- 5. Conclusion
  calc ∑ ξ ∈ (range (2 ^ q)).erase 0, ∑ η : ZMod (3 ^ L),
        ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * (‖D_omega q L ξ η‖ * ‖D_S q s L P η‖ ^ 2)
      ≤ ∑ ξ ∈ (range (2 ^ q)).erase 0, ∑ η : ZMod (3 ^ L), Φ (D_Nrep q L ξ η) :=
        sum_le_sum (fun ξ hξ => sum_le_sum (fun η _ => step1 ξ hξ η))
    _ = ∑ N ∈ A.image (fun p => D_Nrep q L p.1 p.2), Φ N := step2
    _ = ∑ k ∈ range (L + 1), ∑ N ∈ A.image (fun p => D_Nrep q L p.1 p.2),
          (if N ∈ shell q k then D_bnd k * g N else 0) := by rw [hΦ]; exact sum_comm
    _ ≤ ∑ k ∈ range (L + 1), D_bnd k * ∑ N ∈ shell q k, g N := sum_le_sum step3
    _ ≤ ∑ k ∈ range (L + 1), 2 * ((T.card : ℝ) ^ 2 * W * B) := sum_le_sum step4
    _ = 2 * (L + 1) * ((T.card : ℝ) ^ 2) * W * B := by simp; ring

/-- Lemma 5.5 (reduction): `Σ_{ξ≠0} |Ê(ξ)|²|Ĝ(ξ)|² ≤ 4(L+1)² |𝒯|² W B` (with `A_k ≤ B` on every shell). -/
lemma D_lemma55 (hq : 1 ≤ q) (hLp : Lp q ≤ L) (ht : 0 < s - P) (h2t : 2 ^ (s - P) < 3 ^ Lp q)
    (hTne : (Tset q s L P).Nonempty) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ k ≤ L, Ak q s L P k ≤ B) :
    ∑ ξ ∈ (range (2 ^ q)).erase 0,
        ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * ‖Ghat q s L P ξ‖ ^ 2 ≤
      4 * (L + 1) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 * Wsum q (Eset q (hL s L)) * B := by
  have hmain := D_main_sum hq hLp hTne B hB hA
  calc ∑ ξ ∈ (range (2 ^ q)).erase 0, ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * ‖Ghat q s L P ξ‖ ^ 2
      ≤ ∑ ξ ∈ (range (2 ^ q)).erase 0, ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 *
          ((2 * (L + 1)) * ∑ η : ZMod (3 ^ L), ‖D_omega q L ξ η‖ * ‖D_S q s L P η‖ ^ 2) := by
        apply sum_le_sum; intro ξ hξ
        rw [mem_erase, mem_range] at hξ
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (D_Ghat_sq hLp ht h2t ξ).trans ?_
        apply mul_le_mul_of_nonneg_right (D_omega_l1 q L hq hξ.2)
        exact sum_nonneg (fun _ _ => by positivity)
    _ = 2 * (L + 1) * ∑ ξ ∈ (range (2 ^ q)).erase 0, ∑ η : ZMod (3 ^ L),
          ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * (‖D_omega q L ξ η‖ * ‖D_S q s L P η‖ ^ 2) := by
        rw [mul_sum]; apply sum_congr rfl; intro ξ _; rw [mul_sum, mul_sum, mul_sum]
        apply sum_congr rfl; intro η _; ring
    _ ≤ 2 * (L + 1) * (2 * (L + 1) * ((Tset q s L P).card : ℝ) ^ 2 *
          Wsum q (Eset q (hL s L)) * B) := by
        apply mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by ring

/-- `Λ_{L,P} ≤ 4(L+1)² 2^q B/|E|`. -/
lemma D_LamLP_le (hq : 1 ≤ q) (hLp : Lp q ≤ L) (ht : 0 < s - P) (h2t : 2 ^ (s - P) < 3 ^ Lp q)
    (hTne : (Tset q s L P).Nonempty) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ k ≤ L, Ak q s L P k ≤ B) :
    LamLP q s L P ≤ 4 * (L + 1) ^ 2 * (2 : ℝ) ^ q * B / (Eset q (hL s L)).card := by
  have h55 := D_lemma55 hq hLp ht h2t hTne B hB hA
  have hW := D_W_le q (Eset q (hL s L)) (D_Eset_sub q _)
  have hTc : (0 : ℝ) < (Tset q s L P).card := by exact_mod_cast hTne.card_pos
  unfold LamLP
  rcases Nat.eq_zero_or_pos (Eset q (hL s L)).card with hE | hE
  · rw [hE]; simp
  · have hE' : (0 : ℝ) < (Eset q (hL s L)).card := by exact_mod_cast hE
    rw [div_le_div_iff₀ (by positivity) hE']
    calc (∑ ξ ∈ (range (2 ^ q)).erase 0,
          ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * ‖Ghat q s L P ξ‖ ^ 2) * ((Eset q (hL s L)).card : ℝ)
        ≤ (4 * (L + 1) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 * Wsum q (Eset q (hL s L)) * B) *
            ((Eset q (hL s L)).card : ℝ) := mul_le_mul_of_nonneg_right h55 hE'.le
      _ ≤ (4 * (L + 1) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 *
            ((2 : ℝ) ^ q * (Eset q (hL s L)).card) * B) * ((Eset q (hL s L)).card : ℝ) := by
          gcongr
      _ = _ := by ring

end Reduce

end Collatz.M1
