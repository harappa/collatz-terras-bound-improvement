import CollatzProof.M1.C_Count

/-!
# Auxiliary (5) for Theorem A: slice classes, the splitting identity (Lemma 3.1), multiplicity (Lemma 2.6)

The class `(L, P)`: those `n < 2^s` whose word `u` of length `s` survives from height 0, with `|u| = L`, slice position `P`,
and `T^s(n) mod 2^q ∈ E_L`. By Lemmas 1.5 and 1.9, `#(𝒩_{s+q} ∩ [1, 2^s))` is at most the sum of the class sizes.
For an element `n` of a class: the first-half word `w = u_P(n) ∈ 𝒫_P`, the tail `τ = u_t(T^P n) ∈ 𝒯_{L,P}`,
and the splitting identity `T^s(n) = G(τ) + 3^{L'}(κ(w) + e 3^{L_p})` (`κ(w) = ⟨2^{−t}a_w⟩_{3^{L_p}}`, `e ∈ {0,1}`).
-/

namespace Collatz.M1

open Finset

/-! ## The slice position -/

lemma C_slicePos_spec {k : ℕ} (q : ℕ) (u : Fin k → Bool) :
    (slicePos q u ≥ k ∨ Lp q < ones u (slicePos q u + 1)) ∧
      ∀ m < slicePos q u, ¬ (m ≥ k ∨ Lp q < ones u (m + 1)) := by
  classical
  unfold slicePos
  constructor
  · exact Nat.find_spec (p := fun P => P ≥ k ∨ Lp q < ones u (P + 1)) ⟨k, Or.inl le_rfl⟩
  · intro m hm
    exact Nat.find_min (p := fun P => P ≥ k ∨ Lp q < ones u (P + 1)) ⟨k, Or.inl le_rfl⟩ hm

lemma C_slicePos_le {k : ℕ} (q : ℕ) (u : Fin k → Bool) : slicePos q u ≤ k := by
  by_contra h
  push Not at h
  exact (C_slicePos_spec q u).2 k h (Or.inl le_rfl)

/-- If `|u| > L_p`, then `P = slicePos` satisfies `P < k`, `ones u P = L_p`, and `u_P = 1`. -/
lemma C_slicePos_facts {k : ℕ} (q : ℕ) (u : Fin k → Bool) (h : Lp q < ones u k) :
    ∃ hP : slicePos q u < k, ones u (slicePos q u) = Lp q ∧ u ⟨slicePos q u, hP⟩ = true := by
  obtain ⟨h1, h2⟩ := C_slicePos_spec q u
  set P := slicePos q u with hPdef
  have hk : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    rw [C_ones_zero] at h; omega
  have hPk : P < k := by
    by_contra hge
    push Not at hge
    have := h2 (k - 1) (by omega)
    push Not at this
    have e : k - 1 + 1 = k := by omega
    rw [e] at this
    omega
  have hlt : Lp q < ones u (P + 1) := by
    rcases h1 with h1 | h1
    · omega
    · exact h1
  have hle : ones u P ≤ Lp q := by
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · rw [h0, C_ones_zero]; omega
    · have := h2 (P - 1) (by omega)
      push Not at this
      have e : P - 1 + 1 = P := by omega
      rw [e] at this; exact this.2
  refine ⟨hPk, ?_, ?_⟩
  · rw [C_ones_succ u P hPk] at hlt
    split_ifs at hlt <;> omega
  · rw [C_ones_succ u P hPk] at hlt
    by_contra hne
    simp [hne] at hlt
    omega

/-! ## Classes -/

/-- The class `(L, P)`. -/
noncomputable def C_cls (s q L P : ℕ) : Finset ℕ := by
  classical
  exact (range (2 ^ s)).filter (fun n => SurvW 0 (pw n s) ∧ o n s = L ∧ slicePos q (pw n s) = P ∧
    T^[s] n % 2 ^ q ∈ Eset q (hL s L))

lemma C_mem_cls {s q L P n : ℕ} : n ∈ C_cls s q L P ↔ n < 2 ^ s ∧ SurvW 0 (pw n s) ∧ o n s = L ∧
    slicePos q (pw n s) = P ∧ T^[s] n % 2 ^ q ∈ Eset q (hL s L) := by
  classical
  simp [C_cls]

lemma C_o_le (n k : ℕ) : o n k ≤ k := by
  have := C_ones_le (pw n k) k
  rwa [C_ones_pw n k k le_rfl] at this

/-- Lemmas 1.5 and 1.9: `#(𝒩_{s+q} ∩ [1, 2^s)) ≤ Σ_{L ≤ s} Σ_{P ≤ s} #(class (L, P))`. -/
lemma C_NK_le (s q : ℕ) :
    NKcount (s + q) (2 ^ s - 1) ≤ ∑ L ∈ range (s + 1), ∑ P ∈ range (s + 1), (C_cls s q L P).card := by
  classical
  set S : Finset ℕ := (range (2 ^ s)).filter
    (fun n => SurvW 0 (pw n s) ∧ T^[s] n % 2 ^ q ∈ Eset q (hL s (o n s))) with hS
  have h1 : NKcount (s + q) (2 ^ s - 1) ≤ S.card := by
    unfold NKcount
    apply Finset.card_le_card
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨h1, h2⟩ := C_surv_split n s q hn.2
    rw [hS, Finset.mem_filter, Finset.mem_range]
    have : n < 2 ^ s := by have := Nat.one_le_two_pow (n := s); omega
    exact ⟨this, h1, C_mem_Eset _ _ _ h2⟩
  refine h1.trans ?_
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => o n s) (t := range (s + 1))]
  · apply Finset.sum_le_sum; intro L _
    rw [Finset.card_eq_sum_card_fiberwise (f := fun n => slicePos q (pw n s)) (t := range (s + 1))]
    · apply Finset.sum_le_sum; intro P _
      apply le_of_eq
      congr 1
      ext n
      rw [C_mem_cls]
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩
        rw [h4] at h3
        exact ⟨h1, h2, h4, h5, h3⟩
      · rintro ⟨h1, h2, h4, h5, h3⟩
        rw [← h4] at h3
        exact ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩
    · intro n _
      simp only [Finset.coe_range, Set.mem_Iio]
      have := C_slicePos_le q (pw n s); omega
  · intro n _
    simp only [Finset.coe_range, Set.mem_Iio]
    have := C_o_le n s; omega

/-! ## Properties of the elements of a class -/

lemma C_Lp_pos (q : ℕ) (hq : 2 ≤ q) : 1 ≤ Lp q := by
  by_contra h
  have h0 : Lp q = 0 := by omega
  have := (Lp_spec q).2
  rw [h0] at this
  have : 4 ≤ 2 ^ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  omega

/-- Survival from height 0, as an integer comparison. -/
lemma C_surv_pow {n k : ℕ} (h : SurvW 0 (pw n k)) : ∀ j ≤ k, 2 ^ j ≤ 3 ^ (o n j) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0; simp [o]
  · have := h j h0 hj
    rw [C_hw_pw _ _ _ _ hj] at this
    exact (C_le_lam_iff j (o n j)).1 (by linarith)

/-- Basic properties of the elements of a class. -/
lemma C_cls_facts {s q L P n : ℕ} (hq : 2 ≤ q) (hqs : q < s) (hn : n ∈ C_cls s q L P) :
    P < s ∧ Lp q < L ∧ o n P = Lp q ∧ T^[P] n % 2 = 1 ∧ 0 ≤ hL s L ∧ 0 < hp q P ∧
      pw n P ∈ Pset q P ∧ pw (T^[P] n) (s - P) ∈ Tset q s L P := by
  classical
  rw [C_mem_cls] at hn
  obtain ⟨hn2, hsurv, hoL, hP, hE⟩ := hn
  have hs1 : 1 ≤ s := by omega
  -- h_L ≥ 0
  have hhL : 0 ≤ hL s L := by
    have := hsurv s hs1 le_rfl
    rw [C_hw_pw _ _ _ _ le_rfl, hoL] at this
    unfold hL; linarith
  -- L > L_p
  have hLLp : Lp q < L := by
    have h1 := (C_Lp_real q).1
    have h2 : (q : ℝ) < s := by exact_mod_cast hqs
    unfold hL at hhL
    have h3 : lam * (Lp q : ℝ) < lam * L := by linarith
    have := (mul_lt_mul_iff_of_pos_left C_lam_pos).1 h3
    exact_mod_cast this
  have hones : Lp q < ones (pw n s) s := by rw [C_ones_pw n s s le_rfl, hoL]; exact hLLp
  obtain ⟨hPs, hoP, hbit⟩ := C_slicePos_facts q (pw n s) hones
  have hbit' : T^[slicePos q (pw n s)] n % 2 = 1 := by
    simpa [pw] using hbit
  rw [hP] at hPs hoP hbit'
  rw [C_ones_pw n s P hPs.le] at hoP
  have hLp1 := C_Lp_pos q hq
  -- h_p > 0
  have hhp : 0 < hp q P := by
    have hP1 : 1 ≤ P := by
      have := C_o_le n P; omega
    have hle := C_surv_pow hsurv P hPs.le
    rw [hoP] at hle
    have hne : 2 ^ P ≠ 3 ^ Lp q := by
      intro heq
      have h2 : 2 ∣ 2 ^ P := dvd_pow_self 2 (by omega)
      rw [heq] at h2
      have : ¬ 2 ∣ 3 ^ Lp q := by
        rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.1 (Odd.pow (by decide))
      exact this h2
    have := (C_lt_lam_iff P (Lp q)).2 (lt_of_le_of_ne hle hne)
    unfold hp; linarith
  refine ⟨hPs, hLLp, hoP, hbit', hhL, hhp, ?_, ?_⟩
  · -- the first-half word
    simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by rw [C_ones_pw n P P le_rfl, hoP], ?_⟩
    intro j hj1 hj2
    have := hsurv j hj1 (by omega)
    rw [C_hw_pw _ _ _ _ (by omega)] at this
    rw [C_hw_pw _ _ _ _ hj2]; exact this
  · -- the tail
    simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and]
    have hadd := C_o_add n P (s - P)
    have e : P + (s - P) = s := by omega
    rw [e, hoL, hoP] at hadd
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      simp only [pw, Function.iterate_zero, id_eq]; exact decide_eq_true hbit'
    · rw [C_ones_pw _ _ _ le_rfl]; omega
    · intro j hj1 hj2
      have := hsurv (P + j) (by omega) (by omega)
      rw [C_hw_pw _ _ _ _ (by omega), C_o_add, hoP] at this
      rw [C_hw_pw _ _ _ _ hj2]
      unfold hp
      push_cast at this ⊢
      linarith

/-- On a class, `n ↦ (w, τ)` is injective. -/
lemma C_cls_inj {s q L P : ℕ} (hPs : P ≤ s) {n n' : ℕ} (hn : n ∈ C_cls s q L P)
    (hn' : n' ∈ C_cls s q L P) (h1 : pw n P = pw n' P)
    (h2 : pw (T^[P] n) (s - P) = pw (T^[P] n') (s - P)) : n = n' := by
  rw [C_mem_cls] at hn hn'
  apply C_eq_of_pw s n n' hn.1 hn'.1
  funext i
  by_cases hi : (i : ℕ) < P
  · have := congrFun h1 ⟨i, hi⟩
    simpa [pw] using this
  · have hj : (i : ℕ) - P < s - P := by omega
    have := congrFun h2 ⟨(i : ℕ) - P, hj⟩
    simp only [pw] at this ⊢
    have e : (i : ℕ) = ((i : ℕ) - P) + P := by omega
    rw [e, Function.iterate_add_apply, Function.iterate_add_apply]
    exact this

/-! ## The splitting identity (Lemma 3.1, the form of `G`) -/

lemma C_two_unit (t n : ℕ) : (2 : ZMod (3 ^ n)) ^ t * ((2 : ZMod (3 ^ n)) ^ t)⁻¹ = 1 := by
  apply ZMod.mul_inv_of_unit
  apply IsUnit.pow
  have : IsUnit ((2 : ℕ) : ZMod (3 ^ n)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by norm_num)
  simpa using this

/-- The splitting identity: for an element `n` of a class, `T^s(n) = G(τ) + 3^{L'}(κ(w) + e 3^{L_p})` (`e ∈ {0,1}`). -/
lemma C_split {s q L P n : ℕ} (hq : 2 ≤ q) (hqs : q < s) (hn : n ∈ C_cls s q L P) :
    ∃ e : ℕ, e < 2 ∧ ((T^[s] n : ℕ) : ℤ) = Gstat q s L P (pw (T^[P] n) (s - P)) +
      3 ^ (L - Lp q) * ((inv2mod (s - P) (Lp q) (aOf (pw n P)) : ℤ) + e * 3 ^ Lp q) := by
  obtain ⟨hPs, hLLp, hoP, _, _, _, hw, _⟩ := C_cls_facts hq hqs hn
  have hn' := hn
  rw [C_mem_cls] at hn'
  obtain ⟨hn2, _, hoL, _, _⟩ := hn'
  set t := s - P with ht
  set M := 3 ^ Lp q with hM
  have : NeZero M := ⟨by positivity⟩
  -- first half
  have haw : aOf (pw n P) = T^[P] (n % 2 ^ P) := by unfold aOf; rw [C_mOf_pw]
  have hsplit1 := C_iter_split n P
  rw [hoP, ← haw] at hsplit1
  have hawlt : aOf (pw n P) < M := by
    have := aOf_lt (pw n P); rwa [C_ones_pw n P P le_rfl, hoP] at this
  -- tail
  have hmt : mOf (pw (T^[P] n) t) = T^[P] n % 2 ^ t := C_mOf_pw _ _
  have hat : aOf (pw (T^[P] n) t) = T^[t] (T^[P] n % 2 ^ t) := by unfold aOf; rw [hmt]
  have hsplit2 := C_iter_split (T^[P] n) t
  have hot : o (T^[P] n) t = L - Lp q := by
    have hadd := C_o_add n P t
    have e : P + t = s := by omega
    rw [e, hoL, hoP] at hadd; omega
  rw [hot, ← hat] at hsplit2
  have hTs : T^[s] n = T^[t] (T^[P] n) := by
    have e : s = t + P := by omega
    rw [e, Function.iterate_add_apply]
  -- y < 3^{L_p}
  set y := T^[P] n / 2 ^ t with hy
  have hy_lt : y < M := by
    rw [hy, Nat.div_lt_iff_lt_mul (by positivity)]
    have h1 : n / 2 ^ P < 2 ^ t := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      have e : t + P = s := by omega
      rw [e]; exact hn2
    calc T^[P] n = aOf (pw n P) + M * (n / 2 ^ P) := hsplit1
      _ < M + M * (n / 2 ^ P) := by omega
      _ = M * (n / 2 ^ P + 1) := by ring
      _ ≤ M * 2 ^ t := Nat.mul_le_mul_left _ h1
  -- computation modulo 3^{L_p}
  set g := inv2mod t (Lp q) (mOf (pw (T^[P] n) t)) with hg
  set κ := inv2mod t (Lp q) (aOf (pw n P)) with hκ
  have hg_lt : g < M := ZMod.val_lt _
  have hκ_lt : κ < M := ZMod.val_lt _
  have hu := C_two_unit t (Lp q)
  have hz : ((y + g : ℕ) : ZMod M) = (κ : ZMod M) := by
    have e1 : T^[P] n % 2 ^ t + 2 ^ t * y = T^[P] n := Nat.mod_add_div _ _
    have e2 : ((T^[P] n % 2 ^ t : ℕ) : ZMod M) + (2 : ZMod M) ^ t * (y : ZMod M) =
        (aOf (pw n P) : ZMod M) := by
      have := congrArg (fun m : ℕ => (m : ZMod M)) (e1.trans hsplit1)
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at this
      rw [Nat.cast_pow, Nat.cast_ofNat] at this
      exact this
    have eg : (g : ZMod M) = ((T^[P] n % 2 ^ t : ℕ) : ZMod M) * ((2 : ZMod M) ^ t)⁻¹ := by
      rw [hg]; unfold inv2mod; rw [ZMod.natCast_zmod_val, hmt, Int.cast_natCast]
    have eκ : (κ : ZMod M) = (aOf (pw n P) : ZMod M) * ((2 : ZMod M) ^ t)⁻¹ := by
      rw [hκ]; unfold inv2mod; rw [ZMod.natCast_zmod_val, Int.cast_natCast]
    rw [Nat.cast_add, eg, eκ, ← e2]
    calc (y : ZMod M) + ((T^[P] n % 2 ^ t : ℕ) : ZMod M) * ((2 : ZMod M) ^ t)⁻¹
        = (y : ZMod M) * ((2 : ZMod M) ^ t * ((2 : ZMod M) ^ t)⁻¹) +
            ((T^[P] n % 2 ^ t : ℕ) : ZMod M) * ((2 : ZMod M) ^ t)⁻¹ := by rw [hu, mul_one]
      _ = _ := by ring
  have hmod : (y + g) % M = κ := by
    have := (ZMod.natCast_eq_natCast_iff' (y + g) κ M).1 hz
    rw [this, Nat.mod_eq_of_lt hκ_lt]
  set e := (y + g) / M with he
  refine ⟨e, ?_, ?_⟩
  · rw [he, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  · have hyg : y + g = κ + M * e := by
      have := Nat.mod_add_div (y + g) M; rw [hmod, ← he] at this; omega
    have hT : T^[s] n = aOf (pw (T^[P] n) t) + 3 ^ (L - Lp q) * y := by rw [hTs]; exact hsplit2
    have hyg' : (y : ℤ) + g = κ + (3 : ℤ) ^ Lp q * e := by
      have : ((y + g : ℕ) : ℤ) = ((κ + M * e : ℕ) : ℤ) := by rw [hyg]
      push_cast at this; rw [hM] at this; push_cast at this; exact this
    unfold Gstat
    rw [hT, ← ht, ← hg]
    push_cast
    linear_combination (3 : ℤ) ^ (L - Lp q) * hyg'

/-! ## Multiplicity (Lemma 2.6) -/

/-- The content of Lemma 2.6: if `∀ j ≤ k, 2^j ≤ 3^{o_j}`, then `3 c_k ≤ o_k 3^{o_k}`. -/
lemma C_c_bound (n : ℕ) : ∀ k, (∀ j ≤ k, 2 ^ j ≤ 3 ^ (o n j)) → 3 * c n k ≤ o n k * 3 ^ (o n k) := by
  intro k
  induction k with
  | zero => intro _; simp [c]
  | succ k ih =>
    intro h
    have ih' := ih (fun j hj => h j (by omega))
    have hk := h k (by omega)
    by_cases hodd : T^[k] n % 2 = 1
    · have ho : o n (k + 1) = o n k + 1 := by simp [o, hodd]
      have hc : c n (k + 1) = 3 * c n k + 2 ^ k := by simp [c, hodd]
      rw [ho, hc, pow_succ]
      nlinarith
    · have ho : o n (k + 1) = o n k := by simp [o, hodd]
      have hc : c n (k + 1) = c n k := by simp [c, hodd]
      rw [ho, hc]; exact ih'

lemma C_Pset_mem {q P : ℕ} {w : Fin P → Bool} (hw : w ∈ Pset q P) :
    ones w P = Lp q ∧ SurvW 0 w := by
  classical
  simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw

lemma C_Tset_mem {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) :
    ones τ (s - P) = L - Lp q := by
  classical
  simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
  exact hτ.2.1

lemma C_Pset_sub (q P : ℕ) : Pset q P ⊆ C_W P (Lp q) := by
  intro w hw; rw [C_mem_W]; exact (C_Pset_mem hw).1

lemma C_Tset_sub (q s L P : ℕ) : Tset q s L P ⊆ C_W (s - P) (L - Lp q) := by
  intro τ hτ; rw [C_mem_W]; exact C_Tset_mem hτ

/-- Lemma 2.6: on `𝒫_P`, the multiplicity of `w ↦ κ(w) = ⟨2^{−t}a_w⟩_{3^{L_p}}` is at most `L_p/3 + 1`. -/
lemma C_mult (q P t k : ℕ) :
    ((Pset q P).filter (fun w => inv2mod t (Lp q) (aOf w) = k)).card ≤ Lp q / 3 + 1 := by
  classical
  set F := (Pset q P).filter (fun w => inv2mod t (Lp q) (aOf w) = k) with hF
  set M := 3 ^ Lp q with hM
  have : NeZero M := ⟨by positivity⟩
  have hinj : Set.InjOn (fun w : Fin P → Bool => mOf w) F := by
    intro w _ w' _ h
    have h1 := pw_mOf w
    have h2 := pw_mOf w'
    simp only at h
    rw [← h1, ← h2, h]
  rw [← Finset.card_image_of_injOn hinj]
  apply card_le_of_diam
  intro a ha b hb hab
  rw [Finset.mem_image] at ha hb
  obtain ⟨w, hwF, rfl⟩ := ha
  obtain ⟨w', hwF', rfl⟩ := hb
  rw [hF, Finset.mem_filter] at hwF hwF'
  obtain ⟨hw1, hw2⟩ := C_Pset_mem hwF.1
  obtain ⟨hw1', hw2'⟩ := C_Pset_mem hwF'.1
  -- a_w = a_{w'}
  have haeq : aOf w = aOf w' := by
    have h1 : inv2mod t (Lp q) (aOf w) = inv2mod t (Lp q) (aOf w') := by rw [hwF.2, hwF'.2]
    unfold inv2mod at h1
    have h2 := ZMod.val_injective _ h1
    have h3 : ((aOf w : ℤ) : ZMod M) = ((aOf w' : ℤ) : ZMod M) := by
      have := congrArg (fun x => x * (2 : ZMod M) ^ t) h2
      beta_reduce at this  -- in v4.30 the image under `congrArg` is left without β-reduction
      rwa [mul_assoc, mul_comm _ ((2 : ZMod M) ^ t), C_two_unit, mul_one, mul_assoc,
        mul_comm _ ((2 : ZMod M) ^ t), C_two_unit, mul_one] at this
    push_cast at h3
    have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h3
    have l1 := aOf_lt w; rw [hw1] at l1
    have l2 := aOf_lt w'; rw [hw1'] at l2
    rwa [Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at h4
  -- the upper bound for c
  have hcb : ∀ x : Fin P → Bool, ones x P = Lp q → SurvW 0 x → 3 * cOf x ≤ Lp q * M := by
    intro x hx1 hx2
    have hpw := pw_mOf x
    have hs : SurvW 0 (pw (mOf x) P) := by rw [hpw]; exact hx2
    have := C_c_bound (mOf x) P (C_surv_pow hs)
    have ho : o (mOf x) P = Lp q := by rw [← C_ones_pw (mOf x) P P le_rfl, hpw, hx1]
    rw [ho] at this
    unfold cOf; exact this
  have d1 := dual_word w
  have d2 := dual_word w'
  rw [hw1] at d1
  rw [hw1', ← haeq, d1] at d2
  have hc := hcb w hw1 hw2
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have key : M * (mOf w' - mOf w) ≤ cOf w := by
    have : M * mOf w' + cOf w' = M * mOf w + cOf w := d2.symm
    have e : M * (mOf w' - mOf w) = M * mOf w' - M * mOf w := Nat.mul_sub _ _ _
    omega
  have hMpos : 0 < M := by positivity
  have : M * (3 * (mOf w' - mOf w)) ≤ M * Lp q := by nlinarith
  have := Nat.le_of_mul_le_mul_left this hMpos
  omega

end Collatz.M1
