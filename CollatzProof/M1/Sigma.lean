import CollatzProof.M1.S14

/-!
# §14.5: transfer to the stopping time `σ` (Lemmas 14.2 and 14.3, Theorem 14.4, Corollary 14.5)

The number of `n` with `σ(n) > K` (i.e. `T^j(n) ≥ n` for all `1 ≤ j ≤ K`) is sandwiched between the number of `n` with coefficient stopping time `κ_coef(n) > K` (`NKcount`) and
that number plus the bound on `B_k`. The manuscript bounds `B_k` quasi-polynomially by Corollaire 1 of Laurent–Mignotte–Nesterenko (1995); here instead
we take a Rhin (1987)-type estimate `‖q log₂ 3‖ ≥ C q^{−κ}` (`RhinHyp`) as a hypothesis and bound `B_k` polynomially
(the form of the last item of the "reading" in manuscript §14.5; since `2^{o(K)}` suffices, Theorem 14.4 is unchanged).
`RhinHyp` follows from `Erdos1135.ND.existsPhaseGapRhin` of Mazur's formalization (proved in Lean, `κ = 13.3`) (the bridge in `lean-nd`, `CollatzND/M1Sigma.lean`).
-/

namespace Collatz.M1

open Finset

/-- `σ(n) > K`: `T^j(n) ≥ n` for all `1 ≤ j ≤ K` (`σ` is the stopping time, not the total stopping time). -/
def SigmaGt (n K : ℕ) : Prop := ∀ j : ℕ, 1 ≤ j → j ≤ K → n ≤ T^[j] n

/-- `#{1 ≤ n ≤ X : σ(n) > K}`. -/
noncomputable def SigmaCount (K X : ℕ) : ℕ := by
  classical
  exact ((Icc 1 X).filter (fun n => SigmaGt n K)).card

/-- `#{1 ≤ n ≤ X : σ(n) = ∞}`. -/
noncomputable def DivCount (X : ℕ) : ℕ := by
  classical
  exact ((Icc 1 X).filter (fun n => ∀ K, SigmaGt n K)).card

/-- Rhin-type estimate: there are `C > 0` and `κ` such that `‖q log₂ 3‖ ≥ C q^{−κ}` for all `q ≥ 1` (`‖·‖` is the distance to the nearest integer). -/
def RhinHyp : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q →
    C * (q : ℝ) ^ (-κ) ≤ |(q : ℝ) * lam - (round ((q : ℝ) * lam) : ℝ)|

/-! ## Auxiliary lemmas -/

open Filter Topology

/-- `o_j = Σ_{i<j} [T^i(n) is odd]`. -/
lemma K_o_eq_sum (n j : ℕ) : o n j = ∑ i ∈ range j, (if T^[i] n % 2 = 1 then 1 else 0) := by
  induction j with
  | zero => simp [o]
  | succ j ih => rw [sum_range_succ, ← ih]; simp [o]

/-- The number of 1s among the first `j` letters of the word `pw n K` is `o_j(n)` (`j ≤ K`). -/
lemma K_ones_pw (n K j : ℕ) (hj : j ≤ K) : ones (pw n K) j = o n j := by
  classical
  unfold ones pw
  rw [card_filter, K_o_eq_sum,
    Fin.sum_univ_eq_sum_range (fun i => if i < j ∧ decide (T^[i] n % 2 = 1) = true then 1 else 0) K]
  have e : ∀ i, (if i < j ∧ decide (T^[i] n % 2 = 1) = true then 1 else 0) =
      if i < j then (if T^[i] n % 2 = 1 then 1 else 0) else 0 := by
    intro i; by_cases h1 : i < j <;> by_cases h2 : T^[i] n % 2 = 1 <;> simp [h1, h2]
  simp_rw [e]
  rw [← sum_filter]
  congr 1
  ext i; simp only [mem_filter, mem_range]; omega

/-- `o_j ≤ j`. -/
lemma K_o_le (n j : ℕ) : o n j ≤ j := by
  induction j with
  | zero => simp [o]
  | succ j ih => have := o_succ_le n j; omega

/-- `j ≤ λa ⟺ 2^j ≤ 3^a`. -/
lemma K_lam_le_iff (a j : ℕ) : (j:ℝ) ≤ lam * a ↔ 2 ^ j ≤ 3 ^ a := by
  have h3 : (0:ℝ) < 3 ^ a := by positivity
  have e : lam * a = Real.logb 2 ((3:ℝ) ^ a) := by
    rw [Real.logb_pow, lam]; ring
  rw [e, Real.le_logb_iff_rpow_le (by norm_num) h3, Real.rpow_natCast]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- The height condition is an integer inequality: `0 ≤ y_j ⟺ 2^j ≤ 3^{o_j}` (`j ≤ K`). -/
lemma K_hw_iff (n K j : ℕ) (hj : j ≤ K) : 0 ≤ hw 0 (pw n K) j ↔ 2 ^ j ≤ 3 ^ (o n j) := by
  unfold hw
  rw [K_ones_pw n K j hj, ← K_lam_le_iff]
  constructor <;> intro h <;> linarith


/-- Left part of Lemma 14.2: if `κ_coef(n) > K` (the word survives from height 0), then `σ(n) > K`. -/
lemma K_surv_sigma (n K : ℕ) (h : SurvW 0 (pw n K)) : SigmaGt n K := by
  intro j hj1 hjK
  have h2 := (K_hw_iff n K j hjK).1 (h j hj1 hjK)
  have hd := dual n j
  have : 2 ^ j * n ≤ 2 ^ j * T^[j] n := by
    rw [hd]; nlinarith [Nat.zero_le (c n j), Nat.mul_le_mul_right n h2]
  exact Nat.le_of_mul_le_mul_left this (by positivity)

/-- `2^{−Γ} ≤ 1 − min(Γ,1)/2`, in two cases. -/
lemma K_two_neg (Γ : ℝ) (hΓ : 0 ≤ Γ) : (2:ℝ) ^ (-Γ) ≤ 1 - min Γ 1 / 2 := by
  rcases le_total Γ 1 with h | h
  · rw [min_eq_left h, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num),
      show (2:ℝ)⁻¹ = 1 + (-1/2) by norm_num]
    have := _root_.rpow_one_add_le_one_add_mul_self (s := -1/2) (by norm_num) hΓ h
    linarith
  · rw [min_eq_right h]
    have : (2:ℝ) ^ (-Γ) ≤ (2:ℝ) ^ (-1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at this; linarith

/-- Right part of Lemma 14.2 and Lemma 14.3 (via the Rhin-type estimate): if `σ(n) > K` and the coefficient stopping time is at most `K`, then
`n ≤ (2K/3)(1 + K^{κ'}/C)` (`κ' = max(κ, 0)`). -/
lemma K_sigma_bound (C κ : ℝ) (hC : 0 < C)
    (hRh : ∀ q : ℕ, 0 < q → C * (q : ℝ) ^ (-κ) ≤ |(q : ℝ) * lam - (round ((q : ℝ) * lam) : ℝ)|)
    (n K : ℕ) (hn : 1 ≤ n) (hσ : SigmaGt n K) (hS : ¬ SurvW 0 (pw n K)) :
    (n:ℝ) ≤ (2 * K / 3) * (1 + (K:ℝ) ^ (max κ 0) / C) := by
  classical
  -- coefficient stopping time k (the first time the coefficient drops below 1)
  have hex : ∃ j, 1 ≤ j ∧ j ≤ K ∧ 3 ^ (o n j) < 2 ^ j := by
    unfold SurvW at hS; push Not at hS
    obtain ⟨j, hj1, hjK, hj⟩ := hS
    refine ⟨j, hj1, hjK, ?_⟩
    by_contra hc; push Not at hc
    exact absurd ((K_hw_iff n K j hjK).2 hc) (not_le.2 hj)
  set k := Nat.find hex with hkdef
  obtain ⟨hk1, hkK, hk⟩ := Nat.find_spec hex
  have hmin : ∀ i, 1 ≤ i → i < k → 2 ^ i ≤ 3 ^ (o n i) := by
    intro i hi1 hik
    have := Nat.find_min hex hik
    push Not at this
    exact this hi1 (by omega)
  have hME : MinEnd n k := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp [o]; exact hk.le
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact (Nat.mul_le_mul hk.le (hmin i hpos hlt)).trans_eq (by ring)
    · rw [heq]
  have hc := c_bound n k hME
  have hok := K_o_le n k
  have hd := dual n k
  have hTk := hσ k hk1 hkK
  -- 2^k n ≤ 3^o n + c
  have hmain : 2 ^ k * n ≤ 3 ^ (o n k) * n + c n k := by
    rw [← hd]; exact Nat.mul_le_mul_left _ hTk
  set a := o n k with ha
  -- a ≥ 1
  have ha1 : 1 ≤ a := by
    by_contra h0; push Not at h0
    have ha0 : a = 0 := by omega
    rw [ha0] at hc hmain
    have hc0 : c n k = 0 := by omega
    rw [hc0] at hmain
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    simp at hmain; nlinarith
  -- over the reals
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hkR1 : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hKk : (k:ℝ) ≤ K := by exact_mod_cast hkK
  have haR1 : (1:ℝ) ≤ a := by exact_mod_cast ha1
  have hak : (a:ℝ) ≤ k := by exact_mod_cast hok
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hmainR : (2:ℝ) ^ k * n ≤ 3 ^ a * n + c n k := by exact_mod_cast hmain
  have hcR : 3 * (c n k : ℝ) ≤ a * 2 ^ k := by exact_mod_cast hc
  -- Γ = k − λa > 0
  set Γ := (k:ℝ) - lam * a with hΓ
  have hΓ0 : 0 < Γ := by
    have : ¬ ((k:ℝ) ≤ lam * a) := fun h => absurd ((K_lam_le_iff a k).1 h) (not_le.2 hk)
    push Not at this; linarith
  -- 3^a / 2^k = 2^{−Γ}
  have h3a : (3:ℝ) ^ a = 2 ^ k * (2:ℝ) ^ (-Γ) := by
    rw [hΓ, show -((k:ℝ) - lam * a) = lam * a - k by ring, Real.rpow_sub (by norm_num),
      Real.rpow_natCast, Real.rpow_mul (by norm_num), lam,
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]
    field_simp
  have hg := K_two_neg Γ hΓ0.le
  -- n · min(Γ,1)/2 ≤ k/3
  have hkey : (n:ℝ) * (min Γ 1 / 2) ≤ k / 3 := by
    have h1 : (2:ℝ) ^ k * n * (1 - (2:ℝ) ^ (-Γ)) ≤ c n k := by
      have : (2:ℝ) ^ k * n * (1 - (2:ℝ) ^ (-Γ)) = 2 ^ k * n - 3 ^ a * n := by rw [h3a]; ring
      linarith
    have h2 : (2:ℝ) ^ k * n * (min Γ 1 / 2) ≤ (2:ℝ) ^ k * n * (1 - (2:ℝ) ^ (-Γ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : (c n k : ℝ) ≤ 2 ^ k * (k / 3) := by nlinarith
    have : (2:ℝ) ^ k * ((n:ℝ) * (min Γ 1 / 2)) ≤ 2 ^ k * (k / 3) := by nlinarith
    exact le_of_mul_le_mul_left this h2k
  -- Rhin-type estimate: Γ ≥ C a^{−κ}
  have hRΓ : C * (a:ℝ) ^ (-κ) ≤ Γ := by
    have h1 := hRh a (by omega)
    have h2 := round_le ((a:ℝ) * lam) (k:ℤ)
    have h3 : |(a:ℝ) * lam - ((k:ℤ):ℝ)| = Γ := by
      rw [hΓ, abs_sub_comm]; push_cast; rw [abs_of_pos (by linarith)]; ring
    linarith
  have hapow : (0:ℝ) < (a:ℝ) ^ κ := by positivity
  have hinvΓ : 1 / Γ ≤ (a:ℝ) ^ κ / C := by
    rw [Real.rpow_neg (by positivity)] at hRΓ
    rw [div_le_div_iff₀ hΓ0 hC]
    have : C * ((a:ℝ) ^ κ)⁻¹ * (a:ℝ) ^ κ ≤ Γ * (a:ℝ) ^ κ := mul_le_mul_of_nonneg_right hRΓ hapow.le
    rw [mul_assoc, inv_mul_cancel₀ hapow.ne'] at this; linarith
  have hapK : (a:ℝ) ^ κ ≤ (K:ℝ) ^ (max κ 0) := by
    calc (a:ℝ) ^ κ ≤ (a:ℝ) ^ (max κ 0) := Real.rpow_le_rpow_of_exponent_le haR1 (le_max_left _ _)
      _ ≤ (K:ℝ) ^ (max κ 0) := Real.rpow_le_rpow (by positivity) (hak.trans hKk) (le_max_right _ _)
  -- conclusion
  have hB : 0 ≤ (K:ℝ) ^ (max κ 0) / C := by positivity
  have hdiv : (a:ℝ) ^ κ / C ≤ (K:ℝ) ^ (max κ 0) / C := div_le_div_of_nonneg_right hapK hC.le
  rcases le_total Γ 1 with hΓ1 | hΓ1
  · rw [min_eq_left hΓ1] at hkey
    have : (n:ℝ) ≤ (2 * k / 3) * (1 / Γ) := by
      rw [mul_one_div, le_div_iff₀ hΓ0]; linarith
    calc (n:ℝ) ≤ (2 * k / 3) * (1 / Γ) := this
      _ ≤ (2 * K / 3) * (1 + (K:ℝ) ^ (max κ 0) / C) := by
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  · rw [min_eq_right hΓ1] at hkey
    have : (n:ℝ) ≤ 2 * k / 3 := by linarith
    calc (n:ℝ) ≤ 2 * k / 3 := this
      _ ≤ (2 * K / 3) * (1 + (K:ℝ) ^ (max κ 0) / C) := by nlinarith

/-- A polynomial grows more slowly than an exponential: if `b > 0`, then eventually `C K^κ ≤ 2^{bK}/2`. -/
lemma K_sg_poly (C κ b : ℝ) (hb : 0 < b) :
    ∀ᶠ K : ℕ in atTop, C * (K:ℝ) ^ κ ≤ (2:ℝ) ^ (b * K) / 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero κ (b * Real.log 2)
    (by positivity)).comp tendsto_natCast_atTop_atTop
  have hev := ht.eventually (Iic_mem_nhds (show (0:ℝ) < 1 / (2 * (|C| + 1)) by positivity))
  filter_upwards [hev] with K hK
  simp only [Function.comp_apply] at hK
  have hKp : 0 ≤ (K:ℝ) ^ κ := Real.rpow_nonneg (Nat.cast_nonneg K) κ
  have hexp : 0 < Real.exp (b * Real.log 2 * K) := Real.exp_pos _
  have h1 : (K:ℝ) ^ κ ≤ Real.exp (b * Real.log 2 * K) / (2 * (|C| + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have : (K:ℝ) ^ κ * Real.exp (-(b * Real.log 2) * K) * Real.exp (b * Real.log 2 * K) ≤
        1 / (2 * (|C| + 1)) * Real.exp (b * Real.log 2 * K) :=
      mul_le_mul_of_nonneg_right hK hexp.le
    rw [mul_assoc, ← Real.exp_add, show -(b * Real.log 2) * K + b * Real.log 2 * K = 0 by ring,
      Real.exp_zero, mul_one] at this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at this
    linarith
  have h2 : (2:ℝ) ^ (b * K) = Real.exp (b * Real.log 2 * K) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  rw [h2]
  calc C * (K:ℝ) ^ κ ≤ (|C| + 1) * (K:ℝ) ^ κ :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hKp
    _ ≤ (|C| + 1) * (Real.exp (b * Real.log 2 * K) / (2 * (|C| + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (b * Real.log 2 * K) / 2 := by field_simp

/-- Left inequality of Lemma 14.2 (`κ_coef ≤ σ`, Remark 1.3B). -/
theorem NK_le_sigma (K X : ℕ) : NKcount K X ≤ SigmaCount K X := by
  classical
  unfold NKcount SigmaCount
  apply card_le_card
  intro n hn
  rw [mem_filter] at hn ⊢
  exact ⟨hn.1, K_surv_sigma n K hn.2⟩

/-- Right inequality of Lemma 14.2 and Lemma 14.3 (the bound on `B_k`). From the Rhin-type estimate, `max_{k ≤ K} B_k ≤ C K^κ`. -/
theorem sigma_le_NK (hR : RhinHyp) :
    ∃ C κ : ℝ, 0 < C ∧ 0 ≤ κ ∧ ∀ K X : ℕ, 1 ≤ K →
      (SigmaCount K X : ℝ) ≤ NKcount K X + C * (K : ℝ) ^ κ := by
  classical
  obtain ⟨C, κ, hC, hRh⟩ := hR
  refine ⟨2 / 3 * (1 + 1 / C), 1 + max κ 0, by positivity, by positivity, fun K X hK => ?_⟩
  set B : ℝ := (2 * K / 3) * (1 + (K:ℝ) ^ (max κ 0) / C) with hB
  have hB0 : 0 ≤ B := by positivity
  have hcount : SigmaCount K X ≤ NKcount K X + ⌊B⌋₊ := by
    unfold SigmaCount NKcount
    have hsub : (Icc 1 X).filter (fun n => SigmaGt n K) ⊆
        (Icc 1 X).filter (fun n => SurvW 0 (pw n K)) ∪ Icc 1 ⌊B⌋₊ := by
      intro n hn
      rw [mem_filter] at hn
      rw [mem_union, mem_filter]
      by_cases hS : SurvW 0 (pw n K)
      · exact Or.inl ⟨hn.1, hS⟩
      · right
        have h1 : 1 ≤ n := (mem_Icc.1 hn.1).1
        rw [mem_Icc]
        exact ⟨h1, Nat.le_floor (K_sigma_bound C κ hC hRh n K h1 hn.2 hS)⟩
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [Nat.card_Icc] at this
    -- in v4.30, `convert` also closes the remaining goals, so wrap them in `all_goals`
    convert this using 2
    all_goals omega
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : 1 ≤ (K:ℝ) ^ (max κ 0) := Real.one_le_rpow hK1 (le_max_right _ _)
  have hBK : B ≤ 2 / 3 * (1 + 1 / C) * (K:ℝ) ^ (1 + max κ 0) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one, hB]
    have h1 : (1:ℝ) ≤ (K:ℝ) ^ (max κ 0) := hKp
    have h2 : (2 * K / 3) * (1 + (K:ℝ) ^ (max κ 0) / C) ≤
        (2 * K / 3) * ((K:ℝ) ^ (max κ 0) + (K:ℝ) ^ (max κ 0) / C) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : (2 * K / 3) * ((K:ℝ) ^ (max κ 0) + (K:ℝ) ^ (max κ 0) / C) =
        2 / 3 * (1 + 1 / C) * ((K:ℝ) * (K:ℝ) ^ (max κ 0)) := by field_simp
    linarith
  have hfl : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB0
  have hc' : (SigmaCount K X : ℝ) ≤ (NKcount K X : ℝ) + (⌊B⌋₊ : ℝ) := by exact_mod_cast hcount
  linarith

/-- **Theorem 14.4 (stopping-time version, qualitative form)**: for every `α ∈ (1/2, 0.659]` there is `ε > 0` such that,
for all sufficiently large `K`, `#{n ≤ 2^{αK} : σ(n) > K} ≤ 2^{(α(1−c) − ε)K}`. -/
theorem sigma_main (hBug : BugeaudHyp) (hR : RhinHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
    ∃ ε > 0, ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨ε, hε, K1, hK1⟩ := m1_main hBug α hα hα'
  obtain ⟨C, κ, hC, hκ, hS⟩ := sigma_le_NK hR
  obtain ⟨-, hcc⟩ := cc_bounds
  set a := α * (1 - cc) with ha
  have ha0 : 0 < a := by rw [ha]; nlinarith
  set ε' := min ε a / 2 with hε'
  have hε'0 : 0 < ε' := by rw [hε']; exact half_pos (lt_min hε ha0)
  have hε'ε : ε' ≤ ε / 2 := by rw [hε']; linarith [min_le_left ε a]
  have hε'a : ε' ≤ a / 2 := by rw [hε']; linarith [min_le_right ε a]
  have ev1 := K_sg_poly C κ (a - ε') (by linarith)
  have ev2 : ∀ᶠ K : ℕ in atTop, 1 ≤ (ε - ε') * K := by
    filter_upwards [eventually_ge_atTop ⌈1 / (ε - ε')⌉₊] with K hK
    have h1 : 1 / (ε - ε') ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
    rw [div_le_iff₀ (by linarith)] at h1; linarith
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp ((ev1.and ev2).and (eventually_ge_atTop (max K1 1)))
  refine ⟨ε', hε'0, K0, fun K hK => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hK0 K hK
  have hN := hK1 K (le_trans (le_max_left _ _) h3)
  have hSK := hS K ⌊(2:ℝ) ^ (α * K)⌋₊ (le_trans (le_max_right _ _) h3)
  have h4 : (2:ℝ) ^ ((a - ε) * K) ≤ (2:ℝ) ^ ((a - ε') * K) / 2 := by
    rw [← Real.rpow_sub_one (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have h5 : (2:ℝ) ^ ((a - ε') * K) / 2 + (2:ℝ) ^ ((a - ε') * K) / 2 = (2:ℝ) ^ ((a - ε') * K) := by
    ring
  linarith

/-- **Corollary 14.5 (integers with infinite stopping time, qualitative form)**: there is `ε > 0` such that, for all sufficiently large `x`,
`#{n ≤ x : σ(n) = ∞} ≤ x^{1 − c − ε}`. -/
theorem divergent_count (hBug : BugeaudHyp) (hR : RhinHyp) :
    ∃ ε > 0, ∃ x0 : ℕ, ∀ x ≥ x0, (DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - cc - ε) := by
  classical
  obtain ⟨ε, hε, K0, hK0⟩ := sigma_main hBug hR 0.6 (by norm_num) (by norm_num)
  set α : ℝ := 0.6 with hα
  have hα0 : 0 < α := by norm_num
  set e : ℝ := α * (1 - cc) - ε with he
  refine ⟨ε / (2 * α), by positivity, ?_⟩
  refine ⟨max (max ⌈(2:ℝ) ^ (α * K0)⌉₊ ⌈(2:ℝ) ^ (2 * α * |e| / ε)⌉₊) 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (1:ℝ) ≤ x := by exact_mod_cast hx1
  have hx0 : (0:ℝ) < x := by linarith
  have hxA : (2:ℝ) ^ (α * K0) ≤ x :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  have hxB : (2:ℝ) ^ (2 * α * |e| / ε) ≤ x :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  set Lx := Real.logb 2 x with hLx
  have hL0 : 0 ≤ Lx := Real.logb_nonneg (by norm_num) hxR
  have h2L : (2:ℝ) ^ Lx = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  set K := ⌈Lx / α⌉₊ with hK
  have hK1 : Lx / α ≤ K := Nat.le_ceil _
  have hK2 : (K:ℝ) < Lx / α + 1 := Nat.ceil_lt_add_one (div_nonneg hL0 hα0.le)
  have hLK : Lx ≤ α * K := by rw [div_le_iff₀ hα0] at hK1; linarith
  -- K ≥ K0
  have hKK0 : K0 ≤ K := by
    have : α * K0 ≤ Lx := by
      rw [hLx, Real.le_logb_iff_rpow_le (by norm_num) hx0]; exact hxA
    have : (K0:ℝ) ≤ K := by
      have : (K0:ℝ) ≤ Lx / α := by rw [le_div_iff₀ hα0]; linarith
      linarith
    exact_mod_cast this
  -- x ≤ ⌊2^{αK}⌋
  have hxfl : x ≤ ⌊(2:ℝ) ^ (α * K)⌋₊ := by
    apply Nat.le_floor
    rw [← h2L]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hLK
  have hDiv : DivCount x ≤ SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ := by
    unfold DivCount SigmaCount
    apply card_le_card
    intro n hn
    rw [mem_filter, mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hxfl⟩, hn.2 K⟩
  have hS := hK0 K hKK0
  -- 2^{eK} ≤ 2^{|e|} x^{e/α}
  have h1 : e * K ≤ Lx * (e / α) + |e| := by
    have e1 : Lx * (e / α) = e * (Lx / α) := by ring
    rw [e1]
    rcases le_total 0 e with hpos | hneg
    · rw [abs_of_nonneg hpos]; nlinarith
    · have : e * K ≤ e * (Lx / α) := mul_le_mul_of_nonpos_left hK1 hneg
      linarith [abs_nonneg e]
  have h2 : (2:ℝ) ^ (e * K) ≤ x ^ (e / α) * (2:ℝ) ^ |e| := by
    calc (2:ℝ) ^ (e * K) ≤ (2:ℝ) ^ (Lx * (e / α) + |e|) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = x ^ (e / α) * (2:ℝ) ^ |e| := by
          rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), h2L]
  have h3 : (2:ℝ) ^ |e| ≤ x ^ (ε / (2 * α)) := by
    have := Real.rpow_le_rpow (by positivity) hxB (show 0 ≤ ε / (2 * α) by positivity)
    rw [← Real.rpow_mul (by norm_num), show 2 * α * |e| / ε * (ε / (2 * α)) = |e| by
      field_simp] at this
    exact this
  have h4 : x ^ (e / α) * x ^ (ε / (2 * α)) = (x:ℝ) ^ (1 - cc - ε / (2 * α)) := by
    rw [← Real.rpow_add hx0]; congr 1; rw [he]; field_simp; ring
  have hxe : 0 ≤ (x:ℝ) ^ (e / α) := Real.rpow_nonneg hx0.le _
  calc (DivCount x : ℝ) ≤ SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ := by exact_mod_cast hDiv
    _ ≤ (2:ℝ) ^ (e * K) := hS
    _ ≤ x ^ (e / α) * (2:ℝ) ^ |e| := h2
    _ ≤ x ^ (e / α) * x ^ (ε / (2 * α)) := mul_le_mul_of_nonneg_left h3 hxe
    _ = (x:ℝ) ^ (1 - cc - ε / (2 * α)) := h4

end Collatz.M1
