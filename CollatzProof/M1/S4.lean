import CollatzProof.M1.Counting
import CollatzProof.M1.C_Slice
import CollatzProof.M1.C_Bilin
import CollatzProof.M1.C_Anal

/-! # §4: Theorem A and Corollary A (from (WF) to the improved count)

Assembly of the proof. Uses the auxiliary files `C_Words` (words and numbers), `C_Fourier` (orthogonality and a Parseval-type identity),
`C_Bilin` (the abstract form of Lemma 3.2), `C_Count` (Chernoff-type counting), `C_Slice` (classes, Lemmas 3.1 and 2.6),
`C_Anal` (the gain of `S₃`).

**Differences from the proof in the manuscript (§4)** (same conclusion, constants at least as good as in the manuscript):
- The diagonal term `τ = τ'` of Lemma 3.2 is also included in the Fourier sum, so the first term `2^{−(1−c)(s−q)/2}` is not needed.
- For the second term of `S₁`, instead of the lower bound on `|𝒫_P|` (step 1, slope 1.62), the upper bounds on `|𝒫_P|, |𝒯|, |E|` (Chernoff form) are used directly.
  The gain coefficient is `1 − 1.23((1−c) + t*)/2 ≥ 0.115` (the manuscript has `0.0037`).
- For `S₃`, the gain `1.708δ²q` is shown by a tilted Chernoff form instead of Pinsker's inequality (the manuscript has `1.727`).
  For `S₂`, the same `3.5t* ≥ 1.708` as in the manuscript.

**General forms** (for version 3 of the proof manuscript): `C_cls_S1G`, `C_cls_boundG`, `C_thmAG` and `C_corAG` take as arguments the constants `(a, b)` of `R_δ` (`RdeltaG a b δ`, `WFG a b δ`), the slope `1 + κδ` of `S₃`
and the gain coefficients `g₁` (`S₁`), `g` (`S₂`, `S₃`) and `G` (Corollary A); the lemmas `C_cls_S1`, `C_cls_bound`, `C_thmA`, `C_corA` of version 2 are kept, with unchanged
statements, as their special cases `(a, b, κ, g₁, g, G) = (1.23, 3.5, 10/3, 0.0037, 1.708, 1.70)`.
Version 3 (`(1.38, 4.48, 15/4, 0.0055, 2.18, 2.18)`; the constants of revision r7 of the paper) is in `ThmAV3.lean`.
-/

namespace Collatz.M1

open Finset


/-- `|𝒫_P| ≤ 2^{(1−c)P − t* h_p}`. -/
lemma C_P_card (q P : ℕ) : ((Pset q P).card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * P - tstar * hp q P) := by
  have h1 : ((Pset q P).card : ℝ) ≤ (C_W P (Lp q)).card := by
    exact_mod_cast Finset.card_le_card (C_Pset_sub q P)
  refine h1.trans ((C_W_bound P (Lp q)).trans_eq ?_)
  unfold hp; ring_nf

/-- `|𝒯_{L,P}| ≤ 2^{(1−c)(s−P) − t*(h_L − h_p)}` (`P ≤ s`, `L_p ≤ L`). -/
lemma C_T_card (q s L P : ℕ) (hPs : P ≤ s) (hLL : Lp q ≤ L) :
    ((Tset q s L P).card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * (s - P) - tstar * (hL s L - hp q P)) := by
  have h1 : ((Tset q s L P).card : ℝ) ≤ (C_W (s - P) (L - Lp q)).card := by
    exact_mod_cast Finset.card_le_card (C_Tset_sub q s L P)
  refine h1.trans ((C_W_bound (s - P) (L - Lp q)).trans_eq ?_)
  rw [Nat.cast_sub hPs, Nat.cast_sub hLL]
  unfold hL hp; ring_nf

/-- Tilted form of `|𝒫_P|`. -/
lemma C_P_card_tilt (q P : ℕ) (z : ℝ) (hz : 0 < z) : ((Pset q P).card : ℝ) ≤
    (2:ℝ) ^ ((1 - cc) * P - tstar * hp q P) * ((1 + rhoc * (z - 1)) ^ P / z ^ Lp q) := by
  have h1 : ((Pset q P).card : ℝ) ≤ (C_W P (Lp q)).card := by
    exact_mod_cast Finset.card_le_card (C_Pset_sub q P)
  refine h1.trans ((C_W_bound_tilt P (Lp q) z hz).trans_eq ?_)
  unfold hp; ring_nf

lemma C_rpow_mul_rpow (a b : ℝ) : (2:ℝ) ^ a * (2:ℝ) ^ b = (2:ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

/-- `|𝒫_P||𝒯| ≤ 2^{(1−c)s − t* h_L}`. -/
lemma C_PT_card (q s L P : ℕ) (hPs : P ≤ s) (hLL : Lp q ≤ L) :
    ((Pset q P).card : ℝ) * (Tset q s L P).card ≤ (2:ℝ) ^ ((1 - cc) * s - tstar * hL s L) := by
  calc ((Pset q P).card : ℝ) * (Tset q s L P).card
      ≤ (2:ℝ) ^ ((1 - cc) * P - tstar * hp q P) *
          (2:ℝ) ^ ((1 - cc) * (s - P) - tstar * (hL s L - hp q P)) :=
        mul_le_mul (C_P_card q P) (C_T_card q s L P hPs hLL) (by positivity) (by positivity)
    _ = _ := by rw [C_rpow_mul_rpow]; ring_nf


lemma C_toNat_mod_nat (a q : ℕ) : (((a : ℤ) % 2 ^ q).toNat) = a % 2 ^ q := by
  have : ((2:ℤ) ^ q) = ((2 ^ q : ℕ) : ℤ) := by push_cast; rfl
  rw [this, ← Int.natCast_mod, Int.toNat_natCast]

lemma C_rpow_comb (a1 a2 a3 b : ℝ) (q : ℕ) :
    (2:ℝ) ^ a1 * ((2:ℝ) ^ a2) ^ 2 * ((2:ℝ) ^ a3) ^ 2 * ((2:ℝ) ^ b / 2 ^ q) =
      (2:ℝ) ^ (a1 + 2 * a2 + 2 * a3 + b - q) := by
  rw [div_eq_mul_inv, ← Real.rpow_natCast 2 q, ← Real.rpow_neg (by norm_num), sq, sq]
  simp only [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1; ring

/-- Size of a class ≤ `|𝒫_P||𝒯|`. -/
lemma C_cls_le_PT {s q L P : ℕ} (hq : 2 ≤ q) (hqs : q < s) :
    (C_cls s q L P).card ≤ (Pset q P).card * (Tset q s L P).card := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun n => (pw n P, pw (T^[P] n) (s - P)))
  · intro n hn
    obtain ⟨_, _, _, _, _, _, hw, hτ⟩ := C_cls_facts hq hqs (Finset.mem_coe.1 hn)
    exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨hw, hτ⟩)
  · intro n hn n' hn' h
    have hPs := (C_cls_facts hq hqs (Finset.mem_coe.1 hn)).1
    exact C_cls_inj hPs.le hn hn' (Prod.mk.inj h).1 (Prod.mk.inj h).2

/-- Size of a class ≤ `Σ_{e<2} Σ_{w∈𝒫_P} M_e(κ(w))` (partition identity). -/
lemma C_cls_le_M {s q L P : ℕ} (hq : 2 ≤ q) (hqs : q < s) :
    (C_cls s q L P).card ≤ ∑ e ∈ range 2, ∑ w ∈ Pset q P,
      C_M q (Eset q (hL s L)) (Tset q s L P) (Gstat q s L P) (3 ^ (L - Lp q)) (3 ^ Lp q) e
        (inv2mod (s - P) (Lp q) (aOf w)) := by
  classical
  set E := Eset q (hL s L)
  set Z : ℕ → (Fin P → Bool) × (Fin (s - P) → Bool) → Prop := fun e p =>
    ((Gstat q s L P p.2 + 3 ^ (L - Lp q) * (((inv2mod (s - P) (Lp q) (aOf p.1) : ℕ) : ℤ) +
      (e : ℤ) * 3 ^ Lp q)) % 2 ^ q).toNat ∈ E with hZ
  have h1 : (C_cls s q L P).card ≤
      ((range 2).biUnion (fun e => (Pset q P ×ˢ Tset q s L P).filter (Z e))).card := by
    apply Finset.card_le_card_of_injOn (fun n => (pw n P, pw (T^[P] n) (s - P)))
    · intro n hn
      have hn' := Finset.mem_coe.1 hn
      obtain ⟨_, _, _, _, _, _, hw, hτ⟩ := C_cls_facts hq hqs hn'
      obtain ⟨e, he, hsplit⟩ := C_split hq hqs hn'
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨e, Finset.mem_range.2 he, Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hw, hτ⟩, ?_⟩⟩
      simp only [hZ]
      rw [← hsplit, C_toNat_mod_nat]
      exact (C_mem_cls.1 hn').2.2.2.2
    · intro n hn n' hn' h
      have hPs := (C_cls_facts hq hqs (Finset.mem_coe.1 hn)).1
      exact C_cls_inj hPs.le hn hn' (Prod.mk.inj h).1 (Prod.mk.inj h).2
  refine h1.trans (Finset.card_biUnion_le.trans (le_of_eq ?_))
  apply Finset.sum_congr rfl; intro e _
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl; intro w _
  unfold C_M
  rw [Finset.card_filter]


lemma C_eC_zero : eC 0 = 1 := by unfold eC; simp

/-- Turn the Fourier sum into `|E|²|𝒯|²(1 + Λ)`. -/
lemma C_FS_eq (q s L P : ℕ) (hE : 0 < (Eset q (hL s L)).card) (hT : 0 < (Tset q s L P).card) :
    ∑ ξ ∈ range (2 ^ q), ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 *
        ‖∑ b ∈ Tset q s L P, eC ((ξ : ℝ) * (Gstat q s L P b : ℝ) / 2 ^ q)‖ ^ 2 =
      ((Eset q (hL s L)).card : ℝ) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 * (1 + LamLP q s L P) := by
  have hG : ∀ ξ : ℕ, ∑ b ∈ Tset q s L P, eC ((ξ : ℝ) * (Gstat q s L P b : ℝ) / 2 ^ q) =
      Ghat q s L P ξ := by
    intro ξ; unfold Ghat; simp only [Int.cast_natCast]
  simp_rw [hG]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by positivity : 0 < 2 ^ q))]
  have h0E : Ehat q (Eset q (hL s L)) ((0:ℕ) : ℤ) = ((Eset q (hL s L)).card : ℂ) := by
    unfold Ehat; simp [C_eC_zero]
  have h0G : Ghat q s L P ((0:ℕ) : ℤ) = ((Tset q s L P).card : ℂ) := by
    unfold Ghat; simp [C_eC_zero]
  rw [h0E, h0G]
  have hden : ((Eset q (hL s L)).card : ℝ) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 ≠ 0 := by positivity
  have hL' : ∑ ξ ∈ (range (2 ^ q)).erase 0, ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * ‖Ghat q s L P ξ‖ ^ 2 =
      LamLP q s L P * (((Eset q (hL s L)).card : ℝ) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2) := by
    unfold LamLP; rw [div_mul_cancel₀ _ hden]
  rw [hL']
  simp only [Complex.norm_natCast]
  ring

/-- General form of `S₁` (slices of `RdeltaG a b δ`): the bound on the class size from (WF). The gain coefficient `g₁` satisfies
`1.4381a + 2g₁ ≤ 2` (`(1−c) + t* < 1.4381`). Version 2 has `(a, g₁) = (1.23, 0.0037)`, version 3 has `(1.38, 0.0055)`. -/
lemma C_cls_S1G {s q L P : ℕ} (a b δ g1 : ℝ) (hq : 2 ≤ q) (hqs : q < s) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1e-3) (hag : 1.4381 * a + 2 * g1 ≤ 2)
    (hR : RdeltaG a b δ s q L P) (hWF : LamLP q s L P ≤ (2:ℝ) ^ ((cc - 2 * δ) * q))
    (hne : (C_cls s q L P).Nonempty) :
    ((C_cls s q L P).card : ℝ) ≤ 32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s - g1 * δ * q) := by
  classical
  obtain ⟨n, hn⟩ := hne
  obtain ⟨hPs, hLLp, _, _, hhL, hhp, hwP, hτT⟩ := C_cls_facts hq hqs hn
  obtain ⟨_, hhL2, _, hhp2, _, _, _⟩ := hR
  set E := Eset q (hL s L) with hEdef
  have hEpos : 0 < E.card := Finset.card_pos.2 ⟨_, (C_mem_cls.1 hn).2.2.2.2⟩
  have hTpos : 0 < (Tset q s L P).card := Finset.card_pos.2 ⟨_, hτT⟩
  -- bilinear inequality
  have hK : 3 ^ Lp q ≤ 2 ^ q := (Lp_spec q).1
  have hκ : ∀ w ∈ Pset q P, inv2mod (s - P) (Lp q) (aOf w) < 3 ^ Lp q := by
    intro w _
    have : NeZero (3 ^ Lp q) := ⟨by positivity⟩
    exact ZMod.val_lt _
  have hc1 : IsCoprime ((2:ℤ) ^ q) ((3:ℤ) ^ (L - Lp q)) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have hbil := C_bilin_abstract q E (Pset q P) (fun w => inv2mod (s - P) (Lp q) (aOf w))
    (3 ^ Lp q) (Lp q / 3 + 1) hK hκ (fun k => C_mult q P (s - P) k) (Tset q s L P) (Gstat q s L P)
    (3 ^ (L - Lp q)) (3 ^ Lp q) (by exact_mod_cast hc1)
  rw [C_FS_eq q s L P hEpos hTpos] at hbil
  have hcnt : ((C_cls s q L P).card : ℝ) ≤ ((∑ e ∈ range 2, ∑ w ∈ Pset q P,
      C_M q E (Tset q s L P) (Gstat q s L P) (3 ^ (L - Lp q)) (3 ^ Lp q) e
        (inv2mod (s - P) (Lp q) (aOf w)) : ℕ) : ℝ) := by
    exact_mod_cast C_cls_le_M hq hqs
  have hsq : ((C_cls s q L P).card : ℝ) ^ 2 ≤ 4 * ((Pset q P).card : ℝ) * ((Lp q / 3 + 1 : ℕ) : ℝ) / 2 ^ q *
      ((E.card : ℝ) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 * (1 + LamLP q s L P)) := by
    refine le_trans ?_ hbil
    exact pow_le_pow_left₀ (by positivity) hcnt 2
  -- bounds on each factor
  obtain ⟨hc1', hc2'⟩ := cc_bounds
  obtain ⟨ht1, ht2⟩ := tstar_bounds
  obtain ⟨hl1, hl2⟩ := lam_bounds
  have hLpq : Lp q ≤ q := Nat.findGreatest_le q
  have hm : ((Lp q / 3 + 1 : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by
    have : Lp q / 3 + 1 ≤ q + 1 := by omega
    exact_mod_cast this
  have hA := C_P_card q P
  have hEc : (E.card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * q + tstar * hL s L) := E_upper q (hL s L) hhL
  have hΛ0 : 0 ≤ LamLP q s L P := by unfold LamLP; positivity
  have hTc := C_T_card q s L P hPs.le hLLp.le
  have hΛ : 1 + LamLP q s L P ≤ 2 * (2:ℝ) ^ ((cc - 2 * δ) * q) := by
    have : (1:ℝ) ≤ (2:ℝ) ^ ((cc - 2 * δ) * q) := by
      apply Real.one_le_rpow (by norm_num)
      apply mul_nonneg _ (by positivity); linarith
    linarith
  set X := (1 - cc) * s - g1 * δ * q with hX
  set a1 := (1 - cc) * P - tstar * hp q P
  set a2 := (1 - cc) * q + tstar * hL s L
  set a3 := (1 - cc) * (s - P) - tstar * (hL s L - hp q P)
  have hY : a1 + 2 * a2 + 2 * a3 + (cc - 2 * δ) * q - q ≤ 2 * X + 2 := by
    have hLpr := C_Lp_real q
    have k1 : (1 - cc) * (q - lam * Lp q) ≤ 2 := by
      have h1 : (1 - cc) * (q - lam * Lp q) ≤ (1 - cc) * lam := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith [hLpr.2]
      have h2 : (1 - cc) * lam ≤ 0.95 * 1.585 :=
        mul_le_mul (by linarith) hl2.le (by linarith) (by norm_num)
      linarith
    have k2 : ((1 - cc) + tstar) * hp q P ≤ 1.4381 * (a * δ * q) := by
      apply mul_le_mul (by linarith) hhp2 hhp.le (by norm_num)
    have e : a1 + 2 * a2 + 2 * a3 + (cc - 2 * δ) * q - q =
        2 * ((1 - cc) * s) + (1 - cc) * (q - lam * Lp q) + ((1 - cc) + tstar) * hp q P - 2 * δ * q := by
      simp only [a1, a2, a3]; unfold hp; ring
    rw [e, hX]
    have : 0 ≤ δ * q := by positivity
    have k3 : (1.4381 * a + 2 * g1) * (δ * q) ≤ 2 * (δ * q) := mul_le_mul_of_nonneg_right hag this
    linarith
  have hbound : 4 * ((Pset q P).card : ℝ) * ((Lp q / 3 + 1 : ℕ) : ℝ) / 2 ^ q *
      ((E.card : ℝ) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 * (1 + LamLP q s L P)) ≤
      32 * ((q : ℝ) + 1) * ((2:ℝ) ^ X) ^ 2 := by
    calc 4 * ((Pset q P).card : ℝ) * ((Lp q / 3 + 1 : ℕ) : ℝ) / 2 ^ q *
          ((E.card : ℝ) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2 * (1 + LamLP q s L P))
        = 4 * ((Lp q / 3 + 1 : ℕ) : ℝ) * (((Pset q P).card : ℝ) * (E.card : ℝ) ^ 2 *
            ((Tset q s L P).card : ℝ) ^ 2 * ((1 + LamLP q s L P) / 2 ^ q)) := by ring
      _ ≤ 4 * ((q : ℝ) + 1) * ((2:ℝ) ^ a1 * ((2:ℝ) ^ a2) ^ 2 * ((2:ℝ) ^ a3) ^ 2 *
            ((2 * (2:ℝ) ^ ((cc - 2 * δ) * q)) / 2 ^ q)) := by
          gcongr
      _ = 8 * ((q : ℝ) + 1) * ((2:ℝ) ^ a1 * ((2:ℝ) ^ a2) ^ 2 * ((2:ℝ) ^ a3) ^ 2 *
            ((2:ℝ) ^ ((cc - 2 * δ) * q) / 2 ^ q)) := by ring
      _ = 8 * ((q : ℝ) + 1) * (2:ℝ) ^ (a1 + 2 * a2 + 2 * a3 + (cc - 2 * δ) * q - q) := by
          rw [C_rpow_comb]
      _ ≤ 8 * ((q : ℝ) + 1) * (2:ℝ) ^ (2 * X + 2) := by
          gcongr
          · norm_num
      _ = 32 * ((q : ℝ) + 1) * ((2:ℝ) ^ X) ^ 2 := by
          have e1 : (2:ℝ) ^ (2 * X + 2) = 4 * ((2:ℝ) ^ X) ^ 2 := by
            rw [Real.rpow_add (by norm_num), mul_comm 2 X, Real.rpow_mul (by norm_num),
              Real.rpow_two, Real.rpow_two]
            norm_num; ring
          rw [e1]; ring
  have hfin : ((C_cls s q L P).card : ℝ) ^ 2 ≤ (32 * ((q : ℝ) + 1) * (2:ℝ) ^ X) ^ 2 := by
    have hq1 : (1:ℝ) ≤ 32 * ((q : ℝ) + 1) := by
      have : (0:ℝ) ≤ q := by positivity
      linarith
    calc ((C_cls s q L P).card : ℝ) ^ 2 ≤ 32 * ((q : ℝ) + 1) * ((2:ℝ) ^ X) ^ 2 := hsq.trans hbound
      _ ≤ (32 * ((q : ℝ) + 1)) ^ 2 * ((2:ℝ) ^ X) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [sq]
          have := mul_le_mul_of_nonneg_left hq1 (by positivity : (0:ℝ) ≤ 32 * ((q : ℝ) + 1))
          linarith
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hfin

/-- `S₁` (slices of `R_δ`): bound on the class size from (WF). -/
lemma C_cls_S1 {s q L P : ℕ} (δ : ℝ) (hq : 2 ≤ q) (hqs : q < s) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3)
    (hR : Rdelta δ s q L P) (hWF : LamLP q s L P ≤ (2:ℝ) ^ ((cc - 2 * δ) * q))
    (hne : (C_cls s q L P).Nonempty) :
    ((C_cls s q L P).card : ℝ) ≤ 32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s - 0.0037 * δ * q) :=
  C_cls_S1G 1.23 3.5 δ 0.0037 hq hqs hδ hδ1 (by norm_num) hR hWF hne


/-- General form of the bound per class (combining `S₁`, `S₂`, `S₃`; `RdeltaG a b δ`). The gain of `S₃` comes from the bound `hS3` with slope `1 + κδ`
(of the form of `C_S3_gainG`), the gain of `S₂` from `g ≤ 0.488b` (`t* > 0.488`), and the gain of `S₁` from `1.4381a + 2g₁ ≤ 2`. -/
lemma C_cls_boundG (s q L P : ℕ) (a b δ κ g1 g : ℝ) (hq : 2 ≤ q) (hqs : q < s) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1e-3) (hκδ : 0 < 1 + κ * δ) (hag : 1.4381 * a + 2 * g1 ≤ 2) (hgb : g ≤ 0.488 * b)
    (hS3 : ∀ P Lq q : ℕ, (P : ℝ) ≤ q → a * δ * q ≤ lam * Lq - P →
      (1 + rhoc * ((1 + κ * δ) - 1)) ^ P / (1 + κ * δ) ^ Lq ≤ (2:ℝ) ^ (-(g * δ ^ 2 * q)))
    (hWF : WFG a b δ s q) :
    ((C_cls s q L P).card : ℝ) ≤ 32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s) *
      ((2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q))) := by
  classical
  rcases (C_cls s q L P).eq_empty_or_nonempty with h0 | hne
  · rw [h0, Finset.card_empty, Nat.cast_zero]; positivity
  obtain ⟨n, hn⟩ := hne
  obtain ⟨hPs, hLLp, _, _, hhL, hhp, hwP, hτT⟩ := C_cls_facts hq hqs hn
  obtain ⟨ht1, ht2⟩ := tstar_bounds
  have hq1 : (1:ℝ) ≤ 32 * ((q : ℝ) + 1) := by
    have : (0:ℝ) ≤ q := by positivity
    linarith
  have hpos1 : (0:ℝ) ≤ (2:ℝ) ^ (-(g1 * δ * q)) := by positivity
  have hpos2 : (0:ℝ) ≤ (2:ℝ) ^ (-(g * δ ^ 2 * q)) := by positivity
  -- from the conclusion in the form of `S₂`, `S₃`
  have hfrom23 : ((C_cls s q L P).card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * s) * (2:ℝ) ^ (-(g * δ ^ 2 * q)) →
      ((C_cls s q L P).card : ℝ) ≤ 32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s) *
        ((2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q))) := by
    intro h
    have h2 : (0:ℝ) ≤ (2:ℝ) ^ ((1 - cc) * s) := by positivity
    calc ((C_cls s q L P).card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * s) * (2:ℝ) ^ (-(g * δ ^ 2 * q)) := h
      _ ≤ (2:ℝ) ^ ((1 - cc) * s) * ((2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q))) := by
          apply mul_le_mul_of_nonneg_left _ h2; linarith
      _ ≤ 32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s) *
            ((2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q))) := by
          rw [mul_assoc (32 * ((q : ℝ) + 1))]
          exact le_mul_of_one_le_left (by positivity) hq1
  have hPT : ((C_cls s q L P).card : ℝ) ≤ ((Pset q P).card : ℝ) * (Tset q s L P).card := by
    exact_mod_cast C_cls_le_PT hq hqs
  by_cases h3 : a * δ * q < hp q P
  · -- `S₃`: the height of the first part is large
    apply hfrom23
    have hPq : (P : ℝ) ≤ q := by
      have := (C_Lp_real q).1
      unfold hp at hhp; linarith
    have hgain := hS3 P (Lp q) q hPq (by unfold hp at h3; linarith)
    have hPc := C_P_card_tilt q P (1 + κ * δ) hκδ
    have hTc := C_T_card q s L P hPs.le hLLp.le
    calc ((C_cls s q L P).card : ℝ) ≤ ((Pset q P).card : ℝ) * (Tset q s L P).card := hPT
      _ ≤ ((2:ℝ) ^ ((1 - cc) * P - tstar * hp q P) * (2:ℝ) ^ (-(g * δ ^ 2 * q))) *
            (2:ℝ) ^ ((1 - cc) * (s - P) - tstar * (hL s L - hp q P)) := by
          apply mul_le_mul _ hTc (by positivity) (by positivity)
          exact hPc.trans (mul_le_mul_of_nonneg_left hgain (by positivity))
      _ = (2:ℝ) ^ ((1 - cc) * s - tstar * hL s L) * (2:ℝ) ^ (-(g * δ ^ 2 * q)) := by
          simp only [C_rpow_mul_rpow]
          congr 1; ring
      _ ≤ (2:ℝ) ^ ((1 - cc) * s) * (2:ℝ) ^ (-(g * δ ^ 2 * q)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : 0 ≤ tstar * hL s L := mul_nonneg (by linarith) hhL
          linarith
  · push Not at h3
    by_cases h2 : b * δ ^ 2 * q < hL s L
    · -- `S₂`: the height of the layer is large
      apply hfrom23
      calc ((C_cls s q L P).card : ℝ) ≤ ((Pset q P).card : ℝ) * (Tset q s L P).card := hPT
        _ ≤ (2:ℝ) ^ ((1 - cc) * s - tstar * hL s L) := C_PT_card q s L P hPs.le hLLp.le
        _ ≤ (2:ℝ) ^ ((1 - cc) * s + -(g * δ ^ 2 * q)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have h4 : 0.488 * hL s L ≤ tstar * hL s L := mul_le_mul_of_nonneg_right ht1.le hhL
            have h5 : g * (δ ^ 2 * q) ≤ 0.488 * b * (δ ^ 2 * q) :=
              mul_le_mul_of_nonneg_right hgb (by positivity)
            nlinarith
        _ = (2:ℝ) ^ ((1 - cc) * s) * (2:ℝ) ^ (-(g * δ ^ 2 * q)) := by rw [C_rpow_mul_rpow]
    · -- `S₁`: slices of `R_δ`
      push Not at h2
      have hR : RdeltaG a b δ s q L P := ⟨hhL, h2, hhp, h3, ⟨_, hwP⟩, ⟨_, hτT⟩, hPs⟩
      have h1 := C_cls_S1G a b δ g1 hq hqs hδ hδ1 hag hR (hWF L P hR) ⟨n, hn⟩
      refine h1.trans ?_
      have e : (2:ℝ) ^ ((1 - cc) * s - g1 * δ * q) =
          (2:ℝ) ^ ((1 - cc) * s) * (2:ℝ) ^ (-(g1 * δ * q)) := by
        rw [C_rpow_mul_rpow]; ring_nf
      have h5 : (2:ℝ) ^ (-(g1 * δ * q)) ≤
          (2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q)) := by linarith
      rw [e, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)

/-- Bound per class (combining `S₁`, `S₂`, `S₃`). -/
lemma C_cls_bound (s q L P : ℕ) (δ : ℝ) (hq : 2 ≤ q) (hqs : q < s) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3)
    (hWF : WF δ s q) :
    ((C_cls s q L P).card : ℝ) ≤ 32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s) *
      ((2:ℝ) ^ (-(0.0037 * δ * q)) + (2:ℝ) ^ (-(1.708 * δ ^ 2 * q))) :=
  C_cls_boundG s q L P 1.23 3.5 δ (10 / 3) 0.0037 1.708 hq hqs hδ hδ1 (by positivity) (by norm_num)
    (by norm_num) (fun P Lq q hPq hhp => C_S3_gain δ hδ hδ1 P Lq q hPq hhp) hWF


/-- Concrete form of the general form of Theorem A (`C₀ = 32`, `N₀ = 3`, `q₀ = 2`, `WFG a b δ`):
`#(𝒩_K ∩ [1, 2^s)) ≤ 32(s+2)³ 2^{(1−c)s}(2^{−(1−c)(s−q)/2} + 2^{−g₁δq} + 2^{−gδ²q})`. -/
theorem C_thmAG (s q : ℕ) (a b δ κ g1 g : ℝ) (hq : 2 ≤ q) (hs1 : 1 < (s : ℝ) / q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1e-3) (hκδ : 0 < 1 + κ * δ) (hag : 1.4381 * a + 2 * g1 ≤ 2) (hgb : g ≤ 0.488 * b)
    (hS3 : ∀ P Lq q : ℕ, (P : ℝ) ≤ q → a * δ * q ≤ lam * Lq - P →
      (1 + rhoc * ((1 + κ * δ) - 1)) ^ P / (1 + κ * δ) ^ Lq ≤ (2:ℝ) ^ (-(g * δ ^ 2 * q)))
    (hWF : WFG a b δ s q) :
    (NKcount (s + q) (2 ^ s - 1) : ℝ) ≤ 32 * ((s : ℝ) + 2) ^ 3 * (2:ℝ) ^ ((1 - cc) * s) *
      ((2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(g1 * δ * q)) +
        (2:ℝ) ^ (-(g * δ ^ 2 * q))) := by
  have hq0 : (0:ℝ) < q := by
    have : (2:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hqs : q < s := by
    have := (one_lt_div hq0).1 hs1; exact_mod_cast this
  set B : ℝ := 32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s) *
    ((2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q))) with hB
  have h1 : (NKcount (s + q) (2 ^ s - 1) : ℝ) ≤
      ∑ L ∈ range (s + 1), ∑ P ∈ range (s + 1), ((C_cls s q L P).card : ℝ) := by
    exact_mod_cast C_NK_le s q
  have h2 : ∑ L ∈ range (s + 1), ∑ P ∈ range (s + 1), ((C_cls s q L P).card : ℝ) ≤
      ∑ L ∈ range (s + 1), ∑ P ∈ range (s + 1), B := by
    apply Finset.sum_le_sum; intro L _
    apply Finset.sum_le_sum; intro P _
    exact C_cls_boundG s q L P a b δ κ g1 g hq hqs hδ hδ1 hκδ hag hgb hS3 hWF
  have h3 : ∑ L ∈ range (s + 1), ∑ P ∈ range (s + 1), B = ((s : ℝ) + 1) ^ 2 * B := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  refine h1.trans (h2.trans (h3.le.trans ?_))
  have hT1 : (0:ℝ) ≤ (2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) := by positivity
  have hqs' : (q : ℝ) + 1 ≤ (s : ℝ) + 2 := by
    have : (q : ℝ) < s := by exact_mod_cast hqs
    linarith
  have hs0 : (0:ℝ) ≤ s := by positivity
  have hpoly : ((s : ℝ) + 1) ^ 2 * (32 * ((q : ℝ) + 1)) ≤ 32 * ((s : ℝ) + 2) ^ 3 := by
    have e : 32 * ((s : ℝ) + 2) ^ 3 = ((s : ℝ) + 2) ^ 2 * (32 * ((s : ℝ) + 2)) := by ring
    rw [e]
    apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by positivity); linarith
  have hsum : (2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q)) ≤
      (2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(g1 * δ * q)) +
        (2:ℝ) ^ (-(g * δ ^ 2 * q)) := by linarith
  rw [hB]
  calc ((s : ℝ) + 1) ^ 2 * (32 * ((q : ℝ) + 1) * (2:ℝ) ^ ((1 - cc) * s) *
        ((2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q))))
      = (((s : ℝ) + 1) ^ 2 * (32 * ((q : ℝ) + 1))) * (2:ℝ) ^ ((1 - cc) * s) *
        ((2:ℝ) ^ (-(g1 * δ * q)) + (2:ℝ) ^ (-(g * δ ^ 2 * q))) := by ring
    _ ≤ (32 * ((s : ℝ) + 2) ^ 3) * (2:ℝ) ^ ((1 - cc) * s) *
        ((2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(g1 * δ * q)) +
          (2:ℝ) ^ (-(g * δ ^ 2 * q))) := by
        gcongr

/-- Concrete form of Theorem A (`C₀ = 32`, `N₀ = 3`, `q₀ = 2`). The 1st and 4th terms are not used (see the remark in the text). -/
theorem C_thmA (s q : ℕ) (δ : ℝ) (hq : 2 ≤ q) (hs1 : 1 < (s : ℝ) / q) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3)
    (hWF : WF δ s q) :
    (NKcount (s + q) (2 ^ s - 1) : ℝ) ≤ 32 * ((s : ℝ) + 2) ^ 3 * (2:ℝ) ^ ((1 - cc) * s) *
      ((2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(0.0037 * δ * q)) +
        (2:ℝ) ^ (-(1.708 * δ ^ 2 * q)) + (2:ℝ) ^ (-(1.727 * δ ^ 2 * q))) := by
  have h := C_thmAG s q 1.23 3.5 δ (10 / 3) 0.0037 1.708 hq hs1 hδ hδ1 (by positivity) (by norm_num)
    (by norm_num) (fun P Lq q hPq hhp => C_S3_gain δ hδ hδ1 P Lq q hPq hhp) hWF
  have hT4 : (0:ℝ) ≤ (2:ℝ) ^ (-(1.727 * δ ^ 2 * q)) := by positivity
  refine h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

/-- The content of `sOf_ratio`. -/
theorem C_sOf_ratio (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) (q0 : ℕ) :
    ∃ K0 : ℕ, ∀ K ≥ K0, q0 ≤ K - sOf α K ∧ 1 < (sOf α K : ℝ) / (K - sOf α K : ℕ) ∧
      (sOf α K : ℝ) / (K - sOf α K : ℕ) ≤ 1.94 := by
  set c1 : ℝ := 1.94 - 2.94 * α with hc1
  have hc1pos : 0 < c1 := by rw [hc1]; linarith
  have h1α : 0 < 1 - α := by linarith
  refine ⟨⌈((q0 : ℝ) + 2) / (1 - α)⌉₊ + ⌈2.94 / c1⌉₊ + 1, ?_⟩
  intro K hK
  have hKa : ⌈((q0 : ℝ) + 2) / (1 - α)⌉₊ ≤ K := by omega
  have hKb : ⌈2.94 / c1⌉₊ ≤ K := by omega
  have hK1 : ((q0 : ℝ) + 2) / (1 - α) ≤ K :=
    (Nat.le_ceil _).trans ((Nat.cast_le (α := ℝ)).2 hKa)
  have hK2 : 2.94 / c1 ≤ K :=
    (Nat.le_ceil _).trans ((Nat.cast_le (α := ℝ)).2 hKb)
  have hK1' : (q0 : ℝ) + 2 ≤ (1 - α) * K := by
    rw [div_le_iff₀ h1α] at hK1; linarith
  have hK2' : 2.94 ≤ c1 * K := by
    rw [div_le_iff₀ hc1pos] at hK2; linarith
  have hαK : 0 ≤ α * K := by
    have : (0:ℝ) ≤ K := by positivity
    nlinarith
  have hs1 : (sOf α K : ℝ) ≤ α * K + 1 := by
    unfold sOf; push_cast; linarith [Nat.floor_le hαK]
  have hs2 : α * K < (sOf α K : ℝ) := by
    unfold sOf; push_cast; exact Nat.lt_floor_add_one _
  have hsK : sOf α K ≤ K := by
    have : (sOf α K : ℝ) ≤ K := by
      have : (0:ℝ) ≤ q0 := by positivity
      nlinarith
    exact_mod_cast this
  have hqr : ((K - sOf α K : ℕ) : ℝ) = K - sOf α K := by push_cast [Nat.cast_sub hsK]; ring
  have hq1 : (q0 : ℝ) + 1 ≤ ((K - sOf α K : ℕ) : ℝ) := by rw [hqr]; linarith
  have hqpos : (0:ℝ) < ((K - sOf α K : ℕ) : ℝ) := by
    have : (0:ℝ) ≤ q0 := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (q0 : ℝ) ≤ ((K - sOf α K : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  · rw [one_lt_div hqpos, hqr]
    have : (1 - α) * K < α * K := by
      have : (0:ℝ) < K := by
        have : (0:ℝ) ≤ q0 := by positivity
        nlinarith
      nlinarith
    linarith
  · rw [div_le_iff₀ hqpos, hqr]
    rw [hc1] at hK2'
    nlinarith


lemma C_NK_mono (K X Y : ℕ) (h : X ≤ Y) : NKcount K X ≤ NKcount K Y := by
  classical
  unfold NKcount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans h⟩, hn.2⟩

set_option maxHeartbeats 1000000 in
/-- The content of the general form of Corollary A (`WFG a b δ`, the hypotheses of `C_thmAG`, and the final coefficient `G` with `0 ≤ G ≤ g`, `Gδ ≤ g₁`, `Gδ² ≤ 1`). -/
theorem C_corAG (α a b δ κ g1 g G : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1e-3) (hκδ : 0 < 1 + κ * δ) (hag : 1.4381 * a + 2 * g1 ≤ 2) (hgb : g ≤ 0.488 * b)
    (hS3 : ∀ P Lq q : ℕ, (P : ℝ) ≤ q → a * δ * q ≤ lam * Lq - P →
      (1 + rhoc * ((1 + κ * δ) - 1)) ^ P / (1 + κ * δ) ^ Lq ≤ (2:ℝ) ^ (-(g * δ ^ 2 * q)))
    (hG0 : 0 ≤ G) (hGg : G ≤ g) (hG1 : G * δ ≤ g1) (hG2 : G * δ ^ 2 ≤ 1)
    (hWF : ∃ K1 : ℕ, ∀ K ≥ K1, WFG a b δ (sOf α K) (K - sOf α K)) (ε : ℝ)
    (hε : ε < min (G * δ ^ 2 * (1 - α)) ((1 - cc) * (2 * α - 1) / 2)) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨K1, hK1⟩ := hWF
  obtain ⟨K2, hK2⟩ := C_sOf_ratio α hα hα' 2
  obtain ⟨hc1, hc2⟩ := cc_bounds
  set μ := min (G * δ ^ 2 * (1 - α)) ((1 - cc) * (2 * α - 1) / 2) with hμ
  set η := μ - ε with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set r := (2:ℝ) ^ η with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hη0
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 3 hr1
  have hev : ∀ᶠ K : ℕ in Filter.atTop, (K : ℝ) ^ 3 / r ^ K ≤ 1 / 32768 :=
    ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1 / 32768))
  obtain ⟨K3, hK3⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max K1 K2) (max K3 1), ?_⟩
  intro K hK
  have hK1' : K ≥ K1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK
  have hK2' : K ≥ K2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK
  have hK3' : K ≥ K3 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK
  have hKpos : 1 ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK
  obtain ⟨hq2, hr1', _⟩ := hK2 K hK2'
  set s := sOf α K with hs
  set q := K - s with hq
  have hsK : s + q = K := by omega
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hKpos
  have hαK : 0 ≤ α * K := mul_nonneg (by linarith) (by positivity)
  have hs1 : (s : ℝ) ≤ α * K + 1 := by
    rw [hs]; unfold sOf; push_cast; linarith [Nat.floor_le hαK]
  have hs2 : α * K < (s : ℝ) := by
    rw [hs]; unfold sOf; push_cast; exact Nat.lt_floor_add_one _
  have hqr : (q : ℝ) = K - s := by
    have : (s : ℝ) + q = K := by exact_mod_cast hsK
    linarith
  -- by monotonicity, pass to `[1, 2^{αK}] ⊂ [1, 2^s)`
  have hfl : ⌊(2:ℝ) ^ (α * K)⌋₊ ≤ 2 ^ s - 1 := by
    have h1 : (2:ℝ) ^ (α * K) < (2:ℝ) ^ (s : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs2
    rw [Real.rpow_natCast] at h1
    have h2 : ⌊(2:ℝ) ^ (α * K)⌋₊ < 2 ^ s := by
      rw [Nat.floor_lt (by positivity)]; exact_mod_cast h1
    omega
  have hmono : (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ NKcount (s + q) (2 ^ s - 1) := by
    rw [hsK]; exact_mod_cast C_NK_mono K _ _ hfl
  have hA := C_thmAG s q a b δ κ g1 g hq2 hr1' hδ hδ1 hκδ hag hgb hS3 (hK1 K hK1')
  refine hmono.trans (hA.trans ?_)
  -- bound on the right-hand side
  have h1c : 0 < 1 - cc := by linarith
  have hμ1 : μ ≤ G * δ ^ 2 * (1 - α) := min_le_left _ _
  have hμ2 : μ ≤ (1 - cc) * (2 * α - 1) / 2 := min_le_right _ _
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hqlow : (1 - α) * K - 1 ≤ (q : ℝ) := by rw [hqr]; linarith
  have hkey : μ * K - 1 ≤ G * δ ^ 2 * q := by
    have h1 : μ * K ≤ G * δ ^ 2 * (1 - α) * K := mul_le_mul_of_nonneg_right hμ1 (by linarith)
    have h2 : G * δ ^ 2 * ((1 - α) * K - 1) ≤ G * δ ^ 2 * q :=
      mul_le_mul_of_nonneg_left hqlow (by positivity)
    have e : G * δ ^ 2 * ((1 - α) * K - 1) = G * δ ^ 2 * (1 - α) * K - G * δ ^ 2 := by ring
    linarith
  have hT1 : (2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) ≤ 2 * (2:ℝ) ^ (-(μ * K)) := by
    have : (2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) ≤ (2:ℝ) ^ (-(μ * K)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h1 : μ * K ≤ (1 - cc) * (2 * α - 1) / 2 * K := mul_le_mul_of_nonneg_right hμ2 (by linarith)
      have h2 : (2 * α - 1) * K ≤ (s : ℝ) - q := by rw [hqr]; linarith
      have h3 : (1 - cc) * ((2 * α - 1) * K) ≤ (1 - cc) * ((s : ℝ) - q) :=
        mul_le_mul_of_nonneg_left h2 h1c.le
      have e1 : (1 - cc) * (2 * α - 1) / 2 * K = (1 - cc) * ((2 * α - 1) * K) / 2 := by ring
      have e2 : -((1 - cc) * ((s : ℝ) - q) / 2) = -((1 - cc) * ((s : ℝ) - q)) / 2 := by ring
      rw [e2]; linarith
    have : (0:ℝ) ≤ (2:ℝ) ^ (-(μ * K)) := by positivity
    linarith
  have hTgen : ∀ x : ℝ, G * δ ^ 2 * q ≤ x → (2:ℝ) ^ (-x) ≤ 2 * (2:ℝ) ^ (-(μ * K)) := by
    intro x hx
    calc (2:ℝ) ^ (-x) ≤ (2:ℝ) ^ (1 + -(μ * K)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith
      _ = 2 * (2:ℝ) ^ (-(μ * K)) := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hdq : 0 ≤ δ ^ 2 * q := by positivity
  have hT2 := hTgen (g1 * δ * q) (by
    have h2 : G * δ * (δ * q) ≤ g1 * (δ * q) :=
      mul_le_mul_of_nonneg_right hG1 (by positivity)
    have e1 : G * δ ^ 2 * q = G * δ * (δ * q) := by ring
    have e2 : g1 * δ * q = g1 * (δ * q) := by ring
    rw [e1, e2]; exact h2)
  have hT3 := hTgen (g * δ ^ 2 * q) (by
    have e1 : G * δ ^ 2 * q = G * (δ ^ 2 * q) := by ring
    have e2 : g * δ ^ 2 * q = g * (δ ^ 2 * q) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hGg hdq)
  have hμK : (0:ℝ) ≤ (2:ℝ) ^ (-(μ * K)) := by positivity
  have hsum : (2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(g1 * δ * q)) +
      (2:ℝ) ^ (-(g * δ ^ 2 * q)) ≤ 8 * (2:ℝ) ^ (-(μ * K)) := by
    linarith
  have hpow : (2:ℝ) ^ ((1 - cc) * s) ≤ 2 * (2:ℝ) ^ (α * (1 - cc) * K) := by
    calc (2:ℝ) ^ ((1 - cc) * s) ≤ (2:ℝ) ^ (1 + α * (1 - cc) * K) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : (1 - cc) * (s : ℝ) ≤ (1 - cc) * (α * K + 1) := mul_le_mul_of_nonneg_left hs1 h1c.le
          have e : (1 - cc) * (α * K + 1) = α * (1 - cc) * K + (1 - cc) := by ring
          linarith
      _ = 2 * (2:ℝ) ^ (α * (1 - cc) * K) := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hpoly : ((s : ℝ) + 2) ^ 3 ≤ 64 * (K : ℝ) ^ 3 := by
    have : (s : ℝ) + 2 ≤ 4 * K := by
      have : α * (K : ℝ) ≤ K := mul_le_of_le_one_left (by positivity) (by linarith)
      linarith
    have h0 : (0:ℝ) ≤ (s : ℝ) + 2 := by positivity
    calc ((s : ℝ) + 2) ^ 3 ≤ (4 * (K : ℝ)) ^ 3 := pow_le_pow_left₀ h0 this 3
      _ = 64 * (K : ℝ) ^ 3 := by ring
  have hKr3 := hK3 K hK3'
  have hrK : (0:ℝ) < r ^ K := by positivity
  have hK3b : 32768 * (K : ℝ) ^ 3 ≤ r ^ K := by
    rw [div_le_iff₀ hrK] at hKr3; linarith
  have hrpow : r ^ K = (2:ℝ) ^ (η * K) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc 32 * ((s : ℝ) + 2) ^ 3 * (2:ℝ) ^ ((1 - cc) * s) *
        ((2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(g1 * δ * q)) +
          (2:ℝ) ^ (-(g * δ ^ 2 * q)))
      ≤ 32 * (64 * (K : ℝ) ^ 3) * (2 * (2:ℝ) ^ (α * (1 - cc) * K)) * (8 * (2:ℝ) ^ (-(μ * K))) := by
        gcongr
    _ = (32768 * (K : ℝ) ^ 3) * ((2:ℝ) ^ (α * (1 - cc) * K) * (2:ℝ) ^ (-(μ * K))) := by ring
    _ ≤ r ^ K * ((2:ℝ) ^ (α * (1 - cc) * K) * (2:ℝ) ^ (-(μ * K))) := by
        apply mul_le_mul_of_nonneg_right hK3b (by positivity)
    _ = (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
        rw [hrpow]
        simp only [C_rpow_mul_rpow]
        congr 1; rw [hη]; ring


/-- The content of Corollary A. -/
theorem C_corA (α δ : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) (hδ : 0 < δ) (hδ' : δ ≤ 1e-3)
    (hWF : ∃ K1 : ℕ, ∀ K ≥ K1, WF δ (sOf α K) (K - sOf α K)) (ε : ℝ)
    (hε : ε < min (1.70 * δ ^ 2 * (1 - α)) ((1 - cc) * (2 * α - 1) / 2)) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) :=
  C_corAG α 1.23 3.5 δ (10 / 3) 0.0037 1.708 1.70 hα hα' hδ hδ' (by positivity) (by norm_num) (by norm_num)
    (fun P Lq q hPq hhp => C_S3_gain δ hδ hδ' P Lq q hPq hhp) (by norm_num) (by norm_num)
    (by linarith) (by nlinarith) hWF ε hε


/-- Theorem A: if (WF)(δ) holds at `(s, q)`, then `#(𝒩_K ∩ [1, 2^s))` is at most
`2^{(1−c)s + O(log s)}(2^{−(1−c)(s−q)/2} + 2^{−0.0037δq} + 2^{−1.708δ²q} + 2^{−1.727δ²q})` (`O(log s)` means `C₀(s+2)^{N₀}`). -/
theorem thmA : ∃ C0 : ℝ, ∃ N0 q0 : ℕ, ∀ (s q : ℕ) (δ : ℝ), q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 →
    0 < δ → δ ≤ 1e-3 → WF δ s q →
    (NKcount (s + q) (2 ^ s - 1) : ℝ) ≤ C0 * ((s : ℝ) + 2) ^ N0 * (2:ℝ) ^ ((1 - cc) * s) *
      ((2:ℝ) ^ (-((1 - cc) * (s - q) / 2)) + (2:ℝ) ^ (-(0.0037 * δ * q)) +
        (2:ℝ) ^ (-(1.708 * δ ^ 2 * q)) + (2:ℝ) ^ (-(1.727 * δ ^ 2 * q))) :=
  ⟨32, 3, 2, fun s q δ hq hs1 _ hδ hδ1 hWF => C_thmA s q δ hq hs1 hδ hδ1 hWF⟩

/-- The ratio of `s = ⌊αK⌋ + 1` and `q = K − s` tends to `α/(1−α)`: if `α ∈ (1/2, 0.659]`, then for sufficiently large `K`, `q ≥ q₀` and `1 < s/q ≤ 1.94`. -/
theorem sOf_ratio (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) (q0 : ℕ) :
    ∃ K0 : ℕ, ∀ K ≥ K0, q0 ≤ K - sOf α K ∧ 1 < (sOf α K : ℝ) / (K - sOf α K : ℕ) ∧
      (sOf α K : ℝ) / (K - sOf α K : ℕ) ≤ 1.94 :=
  C_sOf_ratio α hα hα' q0

/-- Corollary A: if (WF)(δ) holds for sufficiently large `K`, then for every `ε` less than `min(1.70δ²(1−α), (1−c)(2α−1)/2)`,
`#(𝒩_K ∩ [1, 2^{αK}]) ≤ 2^{(α(1−c) − ε)K}` for sufficiently large `K`. -/
theorem corA (α δ : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) (hδ : 0 < δ) (hδ' : δ ≤ 1e-3)
    (hWF : ∃ K1 : ℕ, ∀ K ≥ K1, WF δ (sOf α K) (K - sOf α K)) (ε : ℝ)
    (hε : ε < min (1.70 * δ ^ 2 * (1 - α)) ((1 - cc) * (2 * α - 1) / 2)) :
    ∃ K0 : ℕ, ∀ K ≥ K0, (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) :=
  C_corA α δ hα hα' hδ hδ' hWF ε hε

end Collatz.M1
