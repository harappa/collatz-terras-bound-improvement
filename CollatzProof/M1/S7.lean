import CollatzProof.M1.Counting
import CollatzProof.M1.Compat

/-! # §7: Shallow frequencies -/

namespace Collatz.M1

open Finset

/-! ## Auxiliary: a sum over a shell is a constant multiple of the sum over `ξ ∈ [0, 2^q)` ("each `ξ` is taken `#J_k/2^q` times" in the proof of Lemma 7.4) -/

/-- An integer interval of length `n` takes each residue of `ℤ/n` exactly once. -/
theorem F_sum_Ico_zmod (n : ℕ) [NeZero n] (b : ℤ) (h : ZMod n → ℝ) :
    ∑ N ∈ Ico b (b + n), h (N : ZMod n) = ∑ x : ZMod n, h x := by
  have hn : (0:ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  apply Finset.sum_nbij (fun N : ℤ => (N : ZMod n))
  · intro N _; exact Finset.mem_univ _
  · intro N hN N' hN' hNN
    simp only [coe_Ico, Set.mem_Ico] at hN hN'
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub N N' n).1 hNN
    have : N' - N = 0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  · intro x _
    refine ⟨b + ((x.val : ℤ) - b) % n, ?_, ?_⟩
    · simp only [coe_Ico, Set.mem_Ico]
      have h1 := Int.emod_nonneg ((x.val : ℤ) - b) hn.ne'
      have h2 := Int.emod_lt_of_pos ((x.val : ℤ) - b) hn
      constructor <;> linarith
    · simp only [Int.cast_add, ZMod.intCast_mod, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
      ring
  · intro N _; rfl

/-- An integer interval of length `n·m` takes each residue `m` times. -/
theorem F_sum_Ico_zmod_mul (n : ℕ) [NeZero n] (b : ℤ) (m : ℕ) (h : ZMod n → ℝ) :
    ∑ N ∈ Ico b (b + n * m), h (N : ZMod n) = m * ∑ x : ZMod n, h x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hn : (0:ℤ) ≤ n := by positivity
    have hm : (0:ℤ) ≤ m := by positivity
    rw [show b + (n:ℤ) * ((m + 1 : ℕ) : ℤ) = (b + n * m) + n by push_cast; ring,
      ← Finset.Ico_union_Ico_eq_Ico (b := b + n * m) (by nlinarith) (by linarith),
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _), ih, F_sum_Ico_zmod]
    push_cast; ring

/-- The representatives `x.val` of the elements of `ℤ/n` take each value in `[0, n)` once. -/
theorem F_sum_zmod_val (n : ℕ) [NeZero n] (g : ℕ → ℝ) :
    ∑ x : ZMod n, g x.val = ∑ ξ ∈ range n, g ξ := by
  apply Finset.sum_nbij (fun x : ZMod n => x.val)
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro x _ y _ hxy; exact ZMod.val_injective n hxy
  · intro ξ hξ
    refine ⟨(ξ : ZMod n), Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    exact ZMod.val_cast_of_lt (Finset.mem_range.1 hξ)
  · intro x _; rfl

/-- Multiplication by `3^{−L}` is a permutation of `ℤ/2^q`, so the sum over `ξ_N` is the sum over `[0, 2^q)`. -/
theorem F_sum_zmod_xi (q L : ℕ) (g : ℕ → ℝ) :
    ∑ x : ZMod (2 ^ q), g (x * ((3 : ZMod (2 ^ q)) ^ L)⁻¹).val = ∑ ξ ∈ range (2 ^ q), g ξ := by
  have hcop : Nat.Coprime (3 ^ L) (2 ^ q) := Nat.Coprime.pow _ _ (by norm_num)
  set u := ZMod.unitOfCoprime (3 ^ L) hcop with hu
  have hinv : ((3 : ZMod (2 ^ q)) ^ L)⁻¹ = ((u⁻¹ : (ZMod (2 ^ q))ˣ) : ZMod (2 ^ q)) := by
    rw [← ZMod.inv_coe_unit, hu, ZMod.coe_unitOfCoprime]; push_cast; rfl
  rw [hinv, ← F_sum_zmod_val (2 ^ q) g]
  exact Fintype.sum_equiv (Units.mulRight u⁻¹) _ _ (fun x => rfl)

/-- The sum over `ξ_N` over an interval of length `2^q·m`. -/
theorem F_sum_Ico_xi (q L : ℕ) (b : ℤ) (m : ℕ) (g : ℕ → ℝ) :
    ∑ N ∈ Ico b (b + (2 ^ q : ℕ) * m), g (xiN q L N) = m * ∑ ξ ∈ range (2 ^ q), g ξ := by
  rw [← F_sum_zmod_xi q L g]
  exact F_sum_Ico_zmod_mul (2 ^ q) b m (fun x => g (x * ((3 : ZMod (2 ^ q)) ^ L)⁻¹).val)

/-- The shell `J_k` takes each residue of `ℤ/2^q` the same number of times (once for `k = 0`, `2·3^{k−1}` times for `k ≥ 1`). -/
theorem F_sum_shell (q L k : ℕ) (hq : 1 ≤ q) :
    ∃ m : ℕ, ∀ g : ℕ → ℝ, ∑ N ∈ shell q k, g (xiN q L N) = m * ∑ ξ ∈ range (2 ^ q), g ξ := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hq1 : r + 1 - 1 = r := by omega
  unfold shell
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun g => ?_⟩
    simp only [↓reduceIte]
    rw [hq1, ← F_sum_Ico_xi (r + 1) L _ 1 g]
    congr 2
    push_cast; ring
  · refine ⟨2 * 3 ^ (k - 1), fun g => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    rw [hq1, show k' + 1 - 1 = k' by omega]
    have hX : (0:ℤ) < 2 ^ r * 3 ^ k' := by positivity
    have hdisj : Disjoint (Ico ((2:ℤ) ^ r * 3 ^ k') (2 ^ r * 3 ^ (k' + 1)))
        (Ico (-((2:ℤ) ^ r * 3 ^ (k' + 1))) (-(2 ^ r * 3 ^ k'))) := by
      rw [Finset.disjoint_left]
      intro N h1 h2
      simp only [Finset.mem_Ico] at h1 h2
      linarith
    rw [Finset.sum_union hdisj,
      show ((2:ℤ) ^ r * 3 ^ (k' + 1)) = 2 ^ r * 3 ^ k' + ((2 ^ (r + 1) : ℕ) : ℤ) * (3 ^ k' : ℕ) by
        push_cast; ring,
      show (-((2:ℤ) ^ r * 3 ^ k')) = -(2 ^ r * 3 ^ k' + ((2 ^ (r + 1) : ℕ) : ℤ) * (3 ^ k' : ℕ)) +
        ((2 ^ (r + 1) : ℕ) : ℤ) * (3 ^ k' : ℕ) by ring,
      F_sum_Ico_xi, F_sum_Ico_xi]
    push_cast; ring

/-- The Riesz product lies in `[0, 1]`. -/
theorem F_riesz_mem (q s P : ℕ) (τ : Fin (s - P) → Bool) (N : ℤ) :
    0 ≤ riesz q s P τ N ∧ riesz q s P τ N ≤ 1 := by
  unfold riesz
  exact ⟨Finset.prod_nonneg (fun k _ => sq_nonneg _),
    cpt_prod_le_one (fun k _ => sq_nonneg _) (fun k _ => Real.cos_sq_le_one _)⟩

/-- The weight `w(N) ≥ 0`. -/
theorem F_wN_nonneg (q s L : ℕ) (N : ℤ) : 0 ≤ wN q s L N := by
  unfold wN; split_ifs <;> positivity

/-- `ϖ_j ≥ 0`. -/
theorem F_varpi_nonneg (q s L j : ℕ) : 0 ≤ varpi q s L j := by
  unfold varpi Wsum
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The per-tail form of Lemma 7.4: if `F ≤ 1`, then `⟨F⟩_k ≤ ϖ_j + ⟨F⟩^{>j}_k`. -/
theorem F_shAvg_split (q s L k j : ℕ) (hq : 1 ≤ q) (F : ℤ → ℝ) (hF1 : ∀ N, F N ≤ 1) :
    shAvg q s L k F ≤ varpi q s L j + shAvgDeep q s L k j F := by
  obtain ⟨m, hm⟩ := F_sum_shell q L k hq
  set E := Eset q (hL s L)
  -- `G ξ = |Ê(ξ)|² 1[ξ ≠ 0]`, `w(N) = G(ξ_N)`
  set G : ℕ → ℝ := fun ξ => if ξ = 0 then 0 else ‖Ehat q E ξ‖ ^ 2 with hG
  have hwG : ∀ N, wN q s L N = G (xiN q L N) := fun N => rfl
  have hsumG : ∀ p : ℕ → Prop, [DecidablePred p] →
      ∑ ξ ∈ range (2 ^ q), (if p ξ then G ξ else 0) =
        ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter p, ‖Ehat q E ξ‖ ^ 2 := by
    intro p _
    rw [Finset.sum_filter,
      ← Finset.sum_erase (s := range (2 ^ q)) (a := 0) (f := fun ξ => if p ξ then G ξ else 0)
        (by simp [hG])]
    refine Finset.sum_congr rfl (fun ξ hξ => ?_)
    rw [Finset.mem_erase] at hξ
    simp [hG, hξ.1]
  -- denominator `Σ_{J_k} w = m W`
  have hden : ∑ N ∈ shell q k, wN q s L N = m * Wsum q E := by
    simp only [hwG]
    rw [hm G, Wsum]
    congr 1
    have := hsumG (fun _ => True)
    simp only [ite_true, Finset.filter_true] at this
    exact this
  -- weight of the shallow part `Σ_{J_k, dep ≤ j} w = m Σ_{dep ≤ j} |Ê|²`
  have hsh : ∑ N ∈ (shell q k).filter (fun N => ¬ j < dep q (xiN q L N)), wN q s L N =
      m * ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => dep q ξ ≤ j), ‖Ehat q E ξ‖ ^ 2 := by
    rw [Finset.sum_filter]
    simp only [hwG, not_lt]
    rw [hm (fun ξ => if dep q ξ ≤ j then G ξ else 0), hsumG]
  have hVN : 0 ≤ ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => dep q ξ ≤ j), ‖Ehat q E ξ‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hW : 0 ≤ Wsum q E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSh : ∑ N ∈ (shell q k).filter (fun N => ¬ j < dep q (xiN q L N)), wN q s L N * F N ≤
      m * ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => dep q ξ ≤ j), ‖Ehat q E ξ‖ ^ 2 := by
    rw [← hsh]
    exact Finset.sum_le_sum (fun N _ => mul_le_of_le_one_right (F_wN_nonneg q s L N) (hF1 N))
  unfold shAvg shAvgDeep varpi
  rw [← Finset.sum_filter_add_sum_filter_not (shell q k) (fun N => j < dep q (xiN q L N))
    (fun N => wN q s L N * F N), add_div, hden, add_comm (_ / _) (_ / (_ * _))]
  apply add_le_add_left
  calc _ ≤ (m * ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => dep q ξ ≤ j),
          ‖Ehat q E ξ‖ ^ 2) / (m * Wsum q E) :=
        div_le_div_of_nonneg_right hSh (mul_nonneg (Nat.cast_nonneg m) hW)
    _ ≤ _ := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · simp only [hm0, Nat.cast_zero, zero_mul, zero_div]; exact div_nonneg hVN hW
        · rw [mul_div_mul_left _ _ (by positivity)]

/-- Lemma 7.4: for every shell `k` and `j ≥ 0`, `A_k ≤ ϖ_j + A_k^{>j}` (`q ≥ 1`). -/
theorem split_depth (q s L P k j : ℕ) (hq : 1 ≤ q) :
    Ak q s L P k ≤ varpi q s L j + AkDeep q s L P k j := by
  -- Apply `F_shAvg_split` (`Π cos² ≤ 1`) for each tail and average over tails (if `|𝒯| = 0`, the averages on both sides are 0).
  unfold Ak AkDeep
  by_cases hT : (Tset q s L P).card = 0
  · simp only [hT, Nat.cast_zero, div_zero, add_zero]
    exact F_varpi_nonneg q s L j
  · have hTpos : (0:ℝ) < (Tset q s L P).card := by exact_mod_cast Nat.pos_of_ne_zero hT
    rw [div_le_iff₀ hTpos, add_mul, div_mul_cancel₀ _ hTpos.ne']
    calc ∑ τ ∈ Tset q s L P, shAvg q s L k (riesz q s P τ)
        ≤ ∑ τ ∈ Tset q s L P, (varpi q s L j + shAvgDeep q s L k j (riesz q s P τ)) :=
          Finset.sum_le_sum (fun τ _ =>
            F_shAvg_split q s L k j hq _ (fun N => (F_riesz_mem q s P τ N).2))
      _ = varpi q s L j * (Tset q s L P).card +
          ∑ τ ∈ Tset q s L P, shAvgDeep q s L k j (riesz q s P τ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## Auxiliary: the shallow part of depth 0 is empty -/

/-- The depth of `ξ ∈ [1, 2^q)` is at least 1 (`v₂(ξ) < q`). -/
theorem F_dep_pos (q ξ : ℕ) (h0 : ξ ≠ 0) (hlt : ξ < 2 ^ q) : 1 ≤ dep q ξ := by
  unfold dep
  rw [Nat.mod_eq_of_lt hlt]
  simp only [h0, ↓reduceIte]
  have : padicValNat 2 ξ < q := by
    have hd : 2 ^ padicValNat 2 ξ ∣ ξ := pow_padicValNat_dvd
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt hle hlt)
  omega

/-- `ϖ₀ = 0`: there is no nonzero frequency of depth `≤ 0`. -/
theorem F_varpi_zero (q s L : ℕ) : varpi q s L 0 = 0 := by
  unfold varpi
  rw [Finset.filter_false_of_mem]
  · simp
  · intro ξ hξ
    rw [Finset.mem_erase, Finset.mem_range] at hξ
    have := F_dep_pos q ξ hξ.1 hξ.2
    omega

/-- General form of Lemma 7.5 (`RdeltaG a b δ`, `bδ² ≤ 3.5×10^{−6}`): let `0 < δ' < c/2`. For all sufficiently large `q`, for each slice
there is `j₀` with `2j₀ < q` and `ϖ_{j₀} ≤ 2^{−δ'q−1}`, and `|E| ≤ 2^{q−1}`. Version 3 has `h_L ≤ 4.48δ²q` (§4.2.3 of version 3 of the manuscript). -/
theorem choose_j0G (a b δ δ' : ℝ) (hbδ : b * δ ^ 2 ≤ 3.5e-6) :
    ∃ q0 : ℕ, ∀ s q L P : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 → RdeltaG a b δ s q L P →
      ∃ j0 : ℕ, 2 * j0 < q ∧ varpi q s L j0 ≤ (2:ℝ) ^ (-(δ' * q) - 1) ∧
        ((Eset q (hL s L)).card : ℝ) ≤ 2 ^ (q - 1) := by
  -- `j₀ = 0` suffices: the depth of `ξ ∈ [1, 2^q)` is at least 1, so `ϖ₀ = 0` (`F_varpi_zero`).
  -- `|E| ≤ 2^{q−1}` follows from Lemma 2.3 and `t*h_L ≤ 0.4881·3.5·10^{−6}q ≤ cq − 1` (`q ≥ 21`).
  refine ⟨21, fun s q L P hq _ _ hR => ⟨0, by omega, ?_, ?_⟩⟩
  · rw [F_varpi_zero]; positivity
  · obtain ⟨hL0, hL1, -⟩ := hR
    have hE := E_upper q (hL s L) hL0
    have hc := cc_bounds
    have ht := tstar_bounds
    have hqr : (21:ℝ) ≤ q := by exact_mod_cast hq
    have hexp : (1 - cc) * q + tstar * hL s L ≤ ((q - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      have h1 : hL s L ≤ 3.5e-6 * q := hL1.trans (mul_le_mul_of_nonneg_right hbδ (by positivity))
      have h2 : tstar * hL s L ≤ 0.4881 * (3.5e-6 * q) :=
        mul_le_mul (le_of_lt ht.2) h1 hL0 (by norm_num)
      nlinarith
    calc ((Eset q (hL s L)).card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * q + tstar * hL s L) := hE
      _ ≤ (2:ℝ) ^ (((q - 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 2 ^ (q - 1) := Real.rpow_natCast 2 (q - 1)

/-- Lemma 7.5 (choice of `j₀`): let `0 < δ ≤ 10^{−3}`, `0 < δ' < c/2`. For sufficiently large `q`, for each slice of `R_δ`
there is `j₀` with `2j₀ < q` and `ϖ_{j₀} ≤ 2^{−δ'q−1}`, and `|E| ≤ 2^{q−1}`. -/
theorem choose_j0 (δ δ' : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) (hδ'0 : 0 < δ') (hδ'c : δ' < cc / 2) :
    ∃ q0 : ℕ, ∀ s q L P : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 → Rdelta δ s q L P →
      ∃ j0 : ℕ, 2 * j0 < q ∧ varpi q s L j0 ≤ (2:ℝ) ^ (-(δ' * q) - 1) ∧
        ((Eset q (hL s L)).card : ℝ) ≤ 2 ^ (q - 1) :=
  choose_j0G 1.23 3.5 δ δ' (by nlinarith)

end Collatz.M1
