import CollatzProof.M1.Thm1Anal

/-!
# Proposition 13.2B (Proposition 15.5 of the paper): window width `c_D ≤ 9×10^{−3}` from Theorem 1 of Bugeaud (2002)

§13.5.2 of version 3 of the proof manuscript (Section 15.4 of the paper). The conclusion of Proposition 13.2 (`hgt` in `S13.lean`, `c_D ≤ 9×10^{−4}`,
assuming Theorem 2) is proved with the hypothesis replaced by the transcription `Bugeaud.Thm1G1 8` of Theorem 1 (`Thm1Defs.lean`),
for `c_D ≤ 9×10^{−3}` (`hgt_thm1`).

The proof follows `hgt` (reduction by the gcd, the case `N₀ = 3^L b₀ − a₀ = 0`, `v = v₂(N₀) ≥ 3`, and the oddness of `a₀`, `b₀`);
only the last step changes: `hgt` distinguishes whether `a₀/(3^e b₀)` and 9 are multiplicatively independent or dependent, whereas here `S₁^B = 1`, so independence is not used,
and both cases are treated together by Theorem 1 (`J1_bug`). The parameters of Theorem 1 are those of the manuscript:
`m = 8`, `g = 1`, `x₁/y₁ = 9/1`, `x₂/y₂ = a₀/(3^e b₀)` (in this representation, not necessarily in lowest terms), `b₁ = ⌊L/2⌋`, `b₂ = 1`,
`L^B = 7`, `R₁^B = 7`, `S₁^B = 1`, `S₂^B = 9`, `K^B = ⌊((1 − 10^{−8})q − 2 log₂ q − 2)/21⌋`, `R₂^B = ⌊7(K^B − 1)/9⌋ + 1`.
Condition (1) is `T1_cond1` in `Thm1Anal.lean` (for `K^B` sufficiently large).
-/

namespace Collatz.M1

open Bugeaud

/-! ## Auxiliary lemmas -/

/-- `logHt 9 1 = log 9`. -/
theorem J1_logHt_nine : logHt 9 1 = Real.log 9 := by
  unfold logHt; norm_num

/-- For sufficiently large `q`: `1 ≤ q`, `10^6 + 10^6 log q ≤ q` and `22K₀ ≤ q`. -/
theorem J1_ev (K0 : ℕ) : ∃ q0 : ℕ, ∀ q : ℕ, q0 ≤ q →
    1 ≤ (q : ℝ) ∧ 1e6 + 1e6 * Real.log q ≤ q ∧ 22 * (K0 : ℝ) ≤ q := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (1 / 2e6) * x := by
    have := Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 1 / 2e6 by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx0] at hx
    exact (le_abs_self _).trans hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, max 2e6 (22 * (K0 : ℝ)) ≤ x := Filter.eventually_ge_atTop _
  obtain ⟨q0, hq0⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (h1.and h2))
  refine ⟨q0, fun q hq => ?_⟩
  obtain ⟨ha, hb⟩ := hq0 q hq
  have hb1 := le_trans (le_max_left _ _) hb
  have hb2 := le_trans (le_max_right _ _) hb
  refine ⟨by linarith, ?_, hb2⟩
  have : 1e6 * Real.log q ≤ 1e6 * ((1 / 2e6) * q) := mul_le_mul_of_nonneg_left ha (by norm_num)
  linarith

/-- `{9^r (x₂/y₂)^s ; r < 7, s < 1}` has 7 elements. -/
theorem J1_card1 (r₂ : ℚ) : (set1 9 r₂ 7 1).card = 7 := by
  unfold set1
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, Finset.card_range]
  rintro ⟨i, j⟩ hi ⟨i', j'⟩ hi' h
  have hj : j < 1 := (Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_coe.1 hi)).2)
  have hj' : j' < 1 := (Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_coe.1 hi')).2)
  have e1 : j = 0 := by omega
  have e2 : j' = 0 := by omega
  subst e1 e2
  simp only [pow_zero, mul_one] at h
  have h' : ((9 ^ i : ℕ) : ℚ) = ((9 ^ i' : ℕ) : ℚ) := by push_cast; exact h
  have h'' : 9 ^ i = 9 ^ i' := by exact_mod_cast h'
  rw [Nat.pow_right_injective (by norm_num : 2 ≤ 9) h'']

/-- `{r + s b₁ ; r < R₂, s < 9}` has `9R₂` elements if `R₂ ≤ b₁`. -/
theorem J1_card2 (b₁ R₂ : ℕ) (h : R₂ ≤ b₁) : (set2 b₁ 1 R₂ 9).card = R₂ * 9 := by
  unfold set2
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, Finset.card_range]
  rintro ⟨i, j⟩ hi ⟨i', j'⟩ hi' hij
  have hi1 : i < R₂ := (Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_coe.1 hi)).1)
  have hi1' : i' < R₂ := (Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_coe.1 hi')).1)
  simp only [mul_one] at hij
  have hb : 0 < b₁ := by omega
  have e1 : i = i' := by
    have := congrArg (· % b₁) hij
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (lt_of_lt_of_le hi1 h),
      Nat.mod_eq_of_lt (lt_of_lt_of_le hi1' h)] at this
    exact this
  have e2 : j = j' := by
    have := congrArg (· / b₁) hij
    simp only [Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt (lt_of_lt_of_le hi1 h),
      Nat.div_eq_of_lt (lt_of_lt_of_le hi1' h), zero_add] at this
    exact this
  rw [e1, e2]

/-! ## Application of Theorem 1 -/

/-- Application of Theorem 1 (`m = 8`, `g = 1`, `x₁/y₁ = 9/1`, `x₂/y₂ = a₀/(3^e b₀)` (`e = L mod 2`), `b₁ = ⌊L/2⌋`, `b₂ = 1`,
`L^B = 7`, `R₁^B = 7`, `S₁^B = 1`, `S₂^B = 9`): if `a₀`, `b₀` are odd, `8 ∣ 3^L b₀ − a₀ ≠ 0`, `K ≥ 3`, `7(K − 1) < 9R₂`,
`R₂ ≤ ⌊L/2⌋` and (1) holds, then `⌊v₂(3^L b₀ − a₀)/3⌋ < 7K`. Multiplicative independence is not used.
`a₀ ≠ 3^e b₀` (`x₂/y₂ ≠ 1`, a premise of `Prem`) is assumed; the case `a₀ = 3^e b₀` is treated separately in `hgt_thm1` (suggested in an independent review). -/
theorem J1_bug (hB1 : Thm1G1 8) (L : ℕ) (hL : 2 ≤ L) (a0 b0 : ℤ) (ha : Odd a0) (hb : Odd b0)
    (h8 : (8 : ℤ) ∣ 3 ^ L * b0 - a0) (hN : 3 ^ L * b0 - a0 ≠ 0) (hne : a0 ≠ 3 ^ (L % 2) * b0)
    (K R₂ : ℕ) (hK : 3 ≤ K) (hR2a : 7 * (K - 1) < 9 * R₂) (hR2b : R₂ ≤ L / 2)
    (hc : 0 < cond1 8 (logHt 9 1) (logHt a0 (3 ^ (L % 2) * b0)) (L / 2) 1 K 7 7 R₂ 1 9) :
    padicValInt 2 (3 ^ L * b0 - a0) / 3 < 7 * K := by
  set e := L % 2 with he
  set b1 := L / 2 with hb1
  have hLe : L = 2 * b1 + e := (Nat.div_add_mod L 2).symm
  set B : ℤ := 3 ^ e * b0 with hB
  have hBo : Odd B := (Odd.pow (by decide)).mul hb
  have hB0 : B ≠ 0 := by rintro h; rw [h] at hBo; exact absurd hBo (by decide)
  have ha0 : a0 ≠ 0 := by rintro rfl; exact absurd ha (by decide)
  set N : ℤ := 3 ^ L * b0 - a0 with hNdef
  -- `3^L b₀ = 9^{b₁} B`
  have h3L : (3 : ℤ) ^ L * b0 = 9 ^ b1 * B := by
    rw [hLe, hB, pow_add, pow_mul]; norm_num; ring
  -- `8 ∣ a₀ − B`
  have h8' : (2 : ℤ) ^ 3 ∣ a0 - B := by
    have h9 : (8 : ℤ) ∣ 9 ^ b1 - 1 := by
      simpa using sub_dvd_pow_sub_pow (9 : ℤ) 1 b1
    have : a0 - B = (9 ^ b1 - 1) * B - N := by rw [hNdef, h3L]; ring
    rw [this]; norm_num
    exact dvd_sub (dvd_mul_of_dvd_left h9 _) h8
  have hvB : padicValInt 2 B = 0 := J_v2_odd hBo
  have hva : padicValInt 2 a0 = 0 := J_v2_odd ha
  have hBq : ((B : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hB0
  have haq : ((a0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast ha0
  set r2 : ℚ := ((a0 : ℤ) : ℚ) / ((B : ℤ) : ℚ) with hr2
  have hr0 : r2 ≠ 0 := div_ne_zero haq hBq
  have e9 : ((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = 9 := by norm_num
  -- `v₂(r₂ − 1) ≥ 3` (`+∞` if `r₂ = 1`)
  have hVr2 : ∀ k : ℤ, k ≤ 3 → VpGe 2 (r2 ^ 1 - 1) k := by
    intro k hk
    by_cases hab : a0 - B = 0
    · left
      rw [pow_one, hr2, show a0 = B by linarith, div_self hBq, sub_self]
    · right
      have hvaB : 3 ≤ padicValInt 2 (a0 - B) := by
        rcases (padicValInt_dvd_iff (p := 2) 3 (a0 - B)).1 (by exact_mod_cast h8') with h | h
        · exact absurd h hab
        · exact h
      have : r2 ^ 1 - 1 = ((a0 - B : ℤ) : ℚ) / ((B : ℤ) : ℚ) := by
        rw [pow_one, hr2]; field_simp; push_cast; ring
      rw [this, padicValRat.div (by exact_mod_cast hab) hBq, padicValRat.of_int, padicValRat.of_int, hvB]
      push_cast; omega
  -- `v₂(9 − 1) = 3`
  have hV9 : ∀ k : ℤ, k ≤ 3 → VpGe 2 ((9 : ℚ) ^ 1 - 1) k := by
    intro k hk
    right
    rw [show (9 : ℚ) ^ 1 - 1 = ((2 ^ 3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat.prime_pow]
    push_cast; omega
  -- the premises
  have hP : Prem 8 (((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) r2 b1 1 K 7 7 R₂ 1 9 := by
    rw [e9]
    simp only [Prem, H1, H2, primeFactors_eight, Finset.mem_singleton, forall_eq, factorization_eight_two]
    refine ⟨by norm_num, by norm_num, hr0, by norm_num, by norm_num, ?_, by omega, by norm_num, ⟨?_, ?_⟩,
      ⟨hV9 3 le_rfl, hVr2 1 (by norm_num)⟩, fun _ => ⟨hV9 2 (by norm_num), hVr2 2 (by norm_num)⟩,
      hK, by norm_num, by norm_num, by omega, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · -- `r₂ ≠ 1`: `a₀ ≠ 3^e b₀`
      rw [hr2]
      intro h1
      rw [div_eq_one_iff_eq hBq] at h1
      exact hne (by exact_mod_cast h1)
    · rw [show (9 : ℚ) = ((9 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]; rfl
    · rw [hr2, padicValRat.div haq hBq, padicValRat.of_int, padicValRat.of_int, hva, hvB]; rfl
    · rw [hExp_one]; norm_num
    · rw [J1_card1]
    · rw [J1_card2 b1 R₂ hR2b]; omega
  -- `Λ = N/B ≠ 0`
  have hx : (((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) ^ b1 - r2 ^ 1 = Rat.divInt N B := by
    rw [e9, ← Rat.intCast_div_eq_divInt, pow_one, hr2, hNdef]
    field_simp
    have : ((3 ^ L * b0 - a0 : ℤ) : ℚ) = ((9 ^ b1 * B - a0 : ℤ) : ℚ) := by rw [h3L]
    push_cast at this ⊢
    rw [this]
  have hΛ : (((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) ^ b1 - r2 ^ 1 ≠ 0 := by
    rw [hx, ← Rat.intCast_div_eq_divInt]
    exact div_ne_zero (by exact_mod_cast hN) hBq
  have key := hB1 9 1 a0 B b1 1 K 7 7 R₂ 1 9 (by norm_num) (by norm_num) ha0 hB0 hP hc hΛ
  -- `v₈(Λ) = ⌊v₂(N)/3⌋`
  have hv8 : vm 8 ((((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) ^ b1 - r2 ^ 1) = ((padicValInt 2 N / 3 : ℕ) : ℤ) := by
    rw [vm_eight, hx]
    set x := Rat.divInt N B with hxdef
    have hxden : padicValNat 2 x.den = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h2
      have h1 : (x.den : ℤ) ∣ B := by rw [hxdef]; exact Rat.den_dvd N B
      have : (2 : ℤ) ∣ B := dvd_trans (by exact_mod_cast h2) h1
      exact absurd hBo (by rw [← Int.not_even_iff_odd, not_not]; exact even_iff_two_dvd.2 this)
    have hxval : (padicValInt 2 x.num : ℤ) = padicValInt 2 N := by
      have h1 : padicValRat 2 x = padicValInt 2 x.num := by
        rw [padicValRat_def, hxden]; simp
      have h2 : padicValRat 2 x = padicValInt 2 N := by
        rw [hxdef, ← Rat.intCast_div_eq_divInt, padicValRat.div (by exact_mod_cast hN) hBq,
          padicValRat.of_int, padicValRat.of_int, hvB]; simp
      rw [← h1, h2]
    have hxval' : padicValInt 2 x.num = padicValInt 2 N := by exact_mod_cast hxval
    unfold v8; rw [hxval', hxden]; simp
  rw [hv8, hMax_one] at key
  generalize padicValInt 2 N / 3 = t at key ⊢
  push_cast at key
  by_contra hcon
  have h7 : ((7 * K : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast (not_lt.1 hcon)
  push_cast at h7
  linarith

/-! ## Non-degeneracy check -/

/-- The premises of `Thm1G1 8` (`Prem`, (1), `Λ ≠ 0`) can be satisfied simultaneously (so the hypothesis is not vacuously true): `x₁/y₁ = 9/1`, `x₂/y₂ = 5/1`, `b₂ = 1`,
`L = 7`, `R₁ = 7`, `S₁ = 1`, `S₂ = 9`, `K` sufficiently large, `R₂ = ⌊7(K − 1)/9⌋ + 1`, `b₁ = R₂`. -/
theorem thm1G1_eight_premises_satisfiable :
    ∃ b₁ K R₂ : ℕ,
      Prem 8 (((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) (((5 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) b₁ 1 K 7 7 R₂ 1 9 ∧
      0 < cond1 8 (logHt 9 1) (logHt 5 1) b₁ 1 K 7 7 R₂ 1 9 ∧
      (((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) ^ b₁ - (((5 : ℤ) : ℚ) / ((1 : ℤ) : ℚ)) ^ 1 ≠ 0 := by
  obtain ⟨K0, hK0⟩ := T1_cond1
  set K := max K0 1000 with hKdef
  have hK1000 : 1000 ≤ K := le_max_right _ _
  set R₂ := 7 * (K - 1) / 9 + 1 with hR₂
  have hR2a : 7 * (K - 1) < 9 * R₂ := by omega
  have hR2b : 9 * R₂ ≤ 7 * (K - 1) + 9 := by omega
  have e9 : ((9 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = 9 := by norm_num
  have e5 : ((5 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = 5 := by norm_num
  refine ⟨R₂, K, R₂, ?_, ?_, ?_⟩
  · rw [e9, e5]
    simp only [Prem, H1, H2, primeFactors_eight, Finset.mem_singleton, forall_eq, factorization_eight_two]
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by omega, by norm_num,
      ⟨pvr_zero_of_not_dvd 2 9 9 (by norm_num) (by norm_num),
        pvr_zero_of_not_dvd 2 5 5 (by norm_num) (by norm_num)⟩,
      ⟨vpGe_of_dvd 2 8 3 _ (by norm_num) (by norm_num) (by norm_num),
        vpGe_of_dvd 2 4 1 _ (by norm_num) (by norm_num) (by norm_num)⟩,
      fun _ => ⟨vpGe_of_dvd 2 8 2 _ (by norm_num) (by norm_num) (by norm_num),
        vpGe_of_dvd 2 4 2 _ (by norm_num) (by norm_num) (by norm_num)⟩,
      by omega, by norm_num, by norm_num, by omega, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · rw [hExp_one]; norm_num
    · rw [J1_card1]
    · rw [J1_card2 R₂ R₂ le_rfl]; omega
  · rw [J1_logHt_nine]
    have h5 : logHt 5 1 = Real.log 5 := by unfold logHt; norm_num
    rw [h5]
    have hKr : (1000 : ℝ) ≤ K := by exact_mod_cast hK1000
    have hR2r : 9 * (R₂ : ℝ) ≤ 7 * K + 2 := by
      have : 9 * R₂ ≤ 7 * K + 2 := by omega
      exact_mod_cast this
    have hl5 : Real.log 5 ≤ 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    exact hK0 K R₂ R₂ (Real.log 5) (le_max_left _ _) hR2a hR2b (by omega) (by linarith)
      (Real.log_nonneg (by norm_num)) (by linarith)
  · rw [e9, e5, pow_one]
    have h9 : (9 : ℕ) ≤ 9 ^ R₂ := by
      obtain ⟨j, hj⟩ : ∃ j, R₂ = j + 1 := ⟨R₂ - 1, by omega⟩
      rw [hj, pow_succ]
      have : 1 ≤ 9 ^ j := Nat.one_le_pow _ _ (by norm_num)
      omega
    have h9q : (9 : ℚ) ≤ 9 ^ R₂ := by exact_mod_cast h9
    intro h
    linarith

/-! ## Proposition 13.2B -/

set_option maxHeartbeats 1000000 in
/-- **Proposition 13.2B** (Proposition 15.5 of the paper): let `1 < s/q ≤ 1.94`, `0 < c_D ≤ 9×10^{−3}`, `D = ⌊c_D q⌋`, `0 ≤ h_L ≤ 10^{−8}q`. For all sufficiently large `q`
(the threshold does not depend on `L`, `s`), if `a ≡ 3^L b (mod 2^{q+D})` and `(a, b) ≠ (0, 0)`, then `max(|a|, |b|) ≥ q2^D(q2^{h_L} + 1)`.
The hypothesis is the transcription `Bugeaud.Thm1G1 8` of Theorem 1 of Bugeaud (2002) (`g = 1`, `m = 8`). The conclusion is the same as that of `hgt` (Proposition 13.2). -/
theorem hgt_thm1 (hB1 : Thm1G1 8) (cD : ℝ) (hcD0 : 0 < cD) (hcD1 : cD ≤ 9e-3) :
    ∃ q0 : ℕ, ∀ s q L : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 → 0 ≤ hL s L →
      hL s L ≤ 1e-8 * q →
      LatticeCond q L ⌊cD * q⌋₊ (q * 2 ^ ⌊cD * q⌋₊ * (q * (2:ℝ) ^ hL s L + 1)) := by
  obtain ⟨K0, hK0⟩ := T1_cond1
  obtain ⟨q0, hq0⟩ := J1_ev K0
  refine ⟨q0, fun s q L hq hs1 hs2 hL0 hL1 a b hab hmod => ?_⟩
  obtain ⟨hq1, hbig, hqK0⟩ := hq0 q hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hmaster : 2000 + 2000 * Real.log q ≤ 0.089 * (q:ℝ) := by linarith
  set D := ⌊cD * q⌋₊ with hD
  set h := hL s L with hh
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hl3a := J_log3_lo
  have hl3b := J_log3_hi
  set ℓ2 := Real.log 2 with hl2
  set ℓ3 := Real.log 3 with hl3
  -- basic facts about `q`, `s`, `L`
  have hq0' : (0:ℝ) < q := by linarith
  have hsq : (q:ℝ) < s := by rwa [one_lt_div hq0'] at hs1
  have hsq2 : (s:ℝ) ≤ 1.94 * q := by rwa [div_le_iff₀ hq0'] at hs2
  have hl2p : 0 < ℓ2 := by linarith
  have hLl : (L:ℝ) * ℓ3 = (s + h) * ℓ2 := by
    have : Real.logb 2 3 * L - s = h := by rw [hh]; rfl
    rw [Real.logb] at this
    field_simp at this
    linarith
  have hX1 : 0.6931471803 * (q:ℝ) ≤ q * ℓ2 := by nlinarith only [hl2a, hq0']
  have hX2 : (q:ℝ) * ℓ2 ≤ 0.6931471808 * q := by nlinarith only [hl2b, hq0']
  have hhl : h * ℓ2 ≤ 1e-8 * (q * ℓ2) := by nlinarith only [hL1, hl2p]
  have hsl : (s:ℝ) * ℓ2 ≤ 1.94 * (q * ℓ2) := by nlinarith only [hsq2, hl2p]
  have hsl' : (q:ℝ) * ℓ2 ≤ s * ℓ2 := by nlinarith only [hsq, hl2p]
  have hhl0 : 0 ≤ h * ℓ2 := by nlinarith only [hL0, hl2p]
  have hDr : (D:ℝ) ≤ cD * q := Nat.floor_le (by positivity)
  have hDl : (D:ℝ) * ℓ2 ≤ 9e-3 * (q * ℓ2) := by
    have : (D:ℝ) ≤ 9e-3 * q := by nlinarith only [hDr, hcD1, hq0']
    nlinarith only [this, hl2p]
  -- `L ≤ 1.2253 q`, `L ≥ 2`
  have hLq : (L:ℝ) ≤ 1.2253 * q := by
    have hL0' : (0:ℝ) ≤ L := by positivity
    have h1 : (L:ℝ) * (19 * ℓ2) ≤ (1.2253 * q) * (19 * ℓ2) := by
      nlinarith only [hLl, hl3a, hL0', hsl, hhl, hX1]
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hL2 : 2 ≤ L := by
    by_contra hc
    have : (L:ℝ) ≤ 1 := by exact_mod_cast (by omega : L ≤ 1)
    have hl3p : 0 < ℓ3 := by linarith
    nlinarith only [this, hl3p, hLl, hsl', hX1, hhl0, hmaster, hlogq, hl3b, hl2b]
  -- `H = 2^D H'`
  have h2h : (1:ℝ) ≤ (2:ℝ) ^ h := Real.one_le_rpow (by norm_num) hL0
  set H' : ℝ := q * (q * (2:ℝ) ^ h + 1) with hH'
  have hHeq : (q:ℝ) * 2 ^ D * (q * (2:ℝ) ^ h + 1) = 2 ^ D * H' := by rw [hH']; ring
  have hq2h : (1:ℝ) ≤ q * (2:ℝ) ^ h := one_le_mul_of_one_le_of_one_le hq1 h2h
  have hH'2 : (q:ℝ) + 1 ≤ H' := by rw [hH']; nlinarith only [hq2h, hq1]
  have hH'1 : (1:ℝ) ≤ H' := by linarith
  set W := Real.log H' with hW
  have hW0 : 0 ≤ W := Real.log_nonneg hH'1
  have hWle : W ≤ ℓ2 + 2 * Real.log q + h * ℓ2 := by
    have h1 : H' ≤ 2 * (q:ℝ) ^ 2 * (2:ℝ) ^ h := by rw [hH']; nlinarith only [hq2h, hq1]
    have h2 : Real.log (2 * (q:ℝ) ^ 2 * (2:ℝ) ^ h) = ℓ2 + 2 * Real.log q + h * ℓ2 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, Real.log_rpow (by norm_num)]
      push_cast; ring
    rw [← h2]; exact Real.log_le_log (by linarith) h1
  have hHpos : (0:ℝ) < 2 ^ D * H' := by positivity
  have hlogH : Real.log (2 ^ D * H') = D * ℓ2 + W := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
  rw [hHeq]
  by_contra hlt
  push Not at hlt
  -- reduce by the gcd: `a = a₀g`, `b = b₀g`, `gcd(a₀, b₀) = 1`
  have hab' : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hab (by rw [hc.1, hc.2])
  obtain ⟨g, a0, b0, hg0, hgcd, rfl, rfl⟩ := Int.exists_gcd_one' (Int.gcd_pos_iff.2 hab')
  set M : ℤ := max |a0 * g| |b0 * g| with hM
  have hg1 : (1:ℤ) ≤ g := by exact_mod_cast hg0
  have hMa : |a0| ≤ M := by
    refine le_trans ?_ (le_max_left _ _)
    rw [abs_mul, Nat.abs_cast]; nlinarith only [abs_nonneg a0, hg1]
  have hMb : |b0| ≤ M := by
    refine le_trans ?_ (le_max_right _ _)
    rw [abs_mul, Nat.abs_cast]; nlinarith only [abs_nonneg b0, hg1]
  have hab0 : a0 ≠ 0 ∨ b0 ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2] at hgcd; simp at hgcd
  have hgM : (g:ℤ) ≤ M := by
    rcases hab0 with h0 | h0
    · refine le_trans ?_ (le_max_left _ _)
      rw [abs_mul, Nat.abs_cast]
      have : 1 ≤ |a0| := Int.one_le_abs h0
      nlinarith only [this, hg1]
    · refine le_trans ?_ (le_max_right _ _)
      rw [abs_mul, Nat.abs_cast]
      have : 1 ≤ |b0| := Int.one_le_abs h0
      nlinarith only [this, hg1]
  have hMH : (M:ℝ) < 2 ^ D * H' := hlt
  -- `2^{q+D} ∣ g N₀`, `N₀ = 3^L b₀ − a₀`
  set N0 : ℤ := 3 ^ L * b0 - a0 with hN0def
  have hdvd : (2:ℤ) ^ (q + D) ∣ (g:ℤ) * N0 := by
    have := hmod.dvd
    have he : 3 ^ L * (b0 * (g:ℤ)) - a0 * g = g * N0 := by rw [hN0def]; ring
    rwa [he] at this
  have hlogHq : D * ℓ2 + W < q * ℓ2 := by
    nlinarith only [hDl, hWle, hhl, hX1, hmaster, hlogq]
  rcases eq_or_ne N0 0 with hN0 | hN0
  · -- `a₀ = 3^L b₀`: `|a| ≥ 3^L > H`, a contradiction
    have hb00 : b0 ≠ 0 := by
      rintro rfl
      rcases hab0 with h0 | h0
      · exact h0 (by rw [hN0def] at hN0; linarith)
      · exact h0 rfl
    have h3a : (3:ℤ) ^ L ≤ |a0| := by
      have : a0 = 3 ^ L * b0 := by rw [hN0def] at hN0; linarith
      rw [this, abs_mul, abs_pow]
      have : 1 ≤ |b0| := Int.one_le_abs hb00
      norm_num
      nlinarith only [this, pow_pos (by norm_num : (0:ℤ) < 3) L]
    have h3r : (3:ℝ) ^ L < 2 ^ D * H' := by
      have : ((3:ℤ) ^ L : ℤ) ≤ M := h3a.trans hMa
      have : ((3:ℝ) ^ L) ≤ (M:ℝ) := by exact_mod_cast this
      linarith
    have := Real.log_lt_log (by positivity) h3r
    rw [Real.log_pow, hlogH] at this
    nlinarith only [this, hLl, hsl', hhl0, hlogHq]
  · -- `N₀ ≠ 0`: for `v = v_2(N₀)`, `2^{q+D} ≤ g2^v < H2^v`, i.e. `q log 2 < W + v log 2`
    set v := padicValInt 2 N0 with hv
    have hb2 := J_dvd_bound g hg0 N0 hN0 (q + D) hdvd
    have hb2r : (2:ℝ) ^ (q + D) ≤ (g:ℝ) * 2 ^ v := by exact_mod_cast hb2
    have hgH : (g:ℝ) < 2 ^ D * H' := by
      have : ((g:ℤ):ℝ) ≤ (M:ℝ) := by exact_mod_cast hgM
      push_cast at this; linarith
    have hmain : (2:ℝ) ^ q < H' * 2 ^ v := by
      have h1 : (2:ℝ) ^ (q + D) < 2 ^ D * H' * 2 ^ v :=
        lt_of_le_of_lt hb2r (mul_lt_mul_of_pos_right hgH (by positivity))
      rw [pow_add] at h1
      have h2 : (2:ℝ) ^ D * 2 ^ q < 2 ^ D * (H' * 2 ^ v) := by linarith
      exact lt_of_mul_lt_mul_left h2 (by positivity)
    have hmainlog : (q:ℝ) * ℓ2 < W + v * ℓ2 := by
      have := Real.log_lt_log (by positivity) hmain
      rw [Real.log_pow, Real.log_mul (by linarith) (by positivity), Real.log_pow] at this
      linarith
    -- `v ≥ 3`: `8 ∣ N₀`, and `a₀`, `b₀` are odd
    have hv3 : 3 ≤ v := by
      have : (3:ℝ) < v := by
        by_contra hc
        push Not at hc
        nlinarith only [hc, hl2p, hmainlog, hWle, hhl, hX1, hmaster, hlogq, hl2b]
      exact_mod_cast this.le
    have h8 : (8:ℤ) ∣ N0 := by
      have := J_dvd_of_le (z := N0) hv3; norm_num at this; exact this
    obtain ⟨hao, hbo⟩ := J_odd_of_coprime L a0 b0 hgcd (dvd_trans (by norm_num) h8)
    have ha0 : a0 ≠ 0 := by rintro rfl; exact absurd hao (by decide)
    have hb0 : b0 ≠ 0 := by rintro rfl; exact absurd hbo (by decide)
    have hl3p : 0 < ℓ3 := by linarith
    -- the case `a₀ = 3^e b₀` (`x₂/y₂ = 1`): `N₀ = 3^e b₀ (3^{2⌊L/2⌋} − 1)`, so the lifting-the-exponent lemma gives `2^v ≤ 4L + 4`,
    -- and `v` is small compared with `q`, a contradiction (Theorem 1 is not used; suggested in an independent review)
    by_cases hEq : a0 = 3 ^ (L % 2) * b0
    · set M := 2 * (L / 2) with hMdef
      have hLM : L = M + L % 2 := by omega
      have hM2 : 2 ≤ M := by omega
      have h3L : (3:ℤ) ^ L = 3 ^ M * 3 ^ (L % 2) := by
        rw [← pow_add]; congr 1
      have hN0f : N0 = (3 ^ (L % 2) * b0) * ((3:ℤ) ^ M - 1) := by
        rw [hN0def, hEq, h3L]
        ring
      have hwo : Odd ((3:ℤ) ^ (L % 2) * b0) := (Odd.pow (by decide)).mul hbo
      have hvM : v = padicValInt 2 ((3:ℤ) ^ M - 1) := by
        rw [hv, hN0f, J_v2_mul_odd hwo]
      have hne3 : (3:ℤ) ^ M - 1 ≠ 0 := by
        have : (3:ℤ) ^ 2 ≤ 3 ^ M := pow_le_pow_right₀ (by norm_num) hM2
        omega
      have hpow := J_v2_pow3_sub M 1 (Or.inl rfl) hne3
      rw [← hvM] at hpow
      have hMLr : (M:ℝ) ≤ L := by exact_mod_cast (by omega : M ≤ L)
      have hpowr : (2:ℝ) ^ v ≤ 4 * (L:ℝ) + 4 := by
        have : ((2 ^ v : ℕ) : ℝ) ≤ ((4 * M + 4 : ℕ) : ℝ) := by exact_mod_cast hpow
        push_cast at this
        linarith
      have hvlog : (v:ℝ) * ℓ2 ≤ Real.log (4 * (L:ℝ) + 4) := by
        have := Real.log_le_log (by positivity) hpowr
        rwa [Real.log_pow] at this
      have h10 : 4 * (L:ℝ) + 4 ≤ 10 * q := by nlinarith only [hLq, hq1]
      have hlog10 : Real.log (4 * (L:ℝ) + 4) ≤ Real.log 10 + Real.log q := by
        rw [← Real.log_mul (by norm_num) (by linarith)]
        exact Real.log_le_log (by positivity) h10
      have hl10 : Real.log 10 < 3 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 10 / 4 by norm_num)
        rw [Real.log_div (by norm_num) (by norm_num)] at this
        have h4 : Real.log 4 = 2 * ℓ2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        linarith
      nlinarith only [hvlog, hlog10, hl10, hmainlog, hWle, hhl, hX1, hmaster, hlogq, hl2b, hl2p]
    -- from here on Theorem 1 (instead of the distinction between the independent and the dependent case in `hgt`)
    -- `K^B = ⌊((1 − 10^{−8})q − 2 log₂ q − 2)/21⌋`
    set KB : ℕ := ⌊((1 - 1e-8) * (q:ℝ) - 2 * Real.log q / ℓ2 - 2) / 21⌋₊ with hKB
    have hlq2 : 2 * Real.log q / ℓ2 * ℓ2 = 2 * Real.log q := by field_simp
    have hKarg : 0 ≤ ((1 - 1e-8) * (q:ℝ) - 2 * Real.log q / ℓ2 - 2) / 21 := by
      apply div_nonneg _ (by norm_num)
      have h1 : 2 * Real.log q / ℓ2 ≤ 3 * Real.log q := by
        rw [div_le_iff₀ hl2p]; nlinarith only [hlogq, hl2a]
      linarith
    have hKB1 : (KB:ℝ) ≤ ((1 - 1e-8) * (q:ℝ) - 2 * Real.log q / ℓ2 - 2) / 21 := Nat.floor_le hKarg
    have hKB2 : ((1 - 1e-8) * (q:ℝ) - 2 * Real.log q / ℓ2 - 2) / 21 < KB + 1 := Nat.lt_floor_add_one _
    -- the form multiplied by `ℓ2`
    have hKBa : 21 * (KB:ℝ) * ℓ2 ≤ (1 - 1e-8) * (q * ℓ2) - 2 * Real.log q - 2 * ℓ2 := by
      have := mul_le_mul_of_nonneg_right hKB1 hl2p.le
      have e : ((1 - 1e-8) * (q:ℝ) - 2 * Real.log q / ℓ2 - 2) / 21 * ℓ2 =
          ((1 - 1e-8) * (q * ℓ2) - 2 * Real.log q / ℓ2 * ℓ2 - 2 * ℓ2) / 21 := by ring
      rw [e, hlq2] at this
      linarith
    have hKBb : (1 - 1e-8) * (q * ℓ2) - 2 * Real.log q - 2 * ℓ2 < 21 * ((KB:ℝ) + 1) * ℓ2 := by
      have := mul_lt_mul_of_pos_right hKB2 hl2p
      have e : ((1 - 1e-8) * (q:ℝ) - 2 * Real.log q / ℓ2 - 2) / 21 * ℓ2 =
          ((1 - 1e-8) * (q * ℓ2) - 2 * Real.log q / ℓ2 * ℓ2 - 2 * ℓ2) / 21 := by ring
      rw [e, hlq2] at this
      linarith
    have hKBq : 0.99 * (q * ℓ2) ≤ 21 * (KB:ℝ) * ℓ2 + 21 * ℓ2 := by
      nlinarith only [hKBb, hbig, hlogq, hX1, hl2b]
    -- `K^B ≥ K₀`, `K^B ≥ 3`
    have hKBK0 : K0 ≤ KB := by
      have h1 : (K0:ℝ) * ℓ2 < ((KB:ℝ) + 1) * ℓ2 := by
        have : 22 * (K0:ℝ) * ℓ2 ≤ q * ℓ2 := mul_le_mul_of_nonneg_right hqK0 hl2p.le
        nlinarith only [this, hKBq, hl2p, hX1, hbig]
      have h2 : (K0:ℝ) < KB + 1 := lt_of_mul_lt_mul_right h1 hl2p.le
      have h3 : K0 < KB + 1 := by exact_mod_cast h2
      omega
    have hKB3 : 3 ≤ KB := by
      have h1 : (3:ℝ) * ℓ2 < ((KB:ℝ) + 1) * ℓ2 := by nlinarith only [hKBq, hbig, hlogq, hX1, hl2p]
      have h2 : (3:ℝ) < KB + 1 := lt_of_mul_lt_mul_right h1 hl2p.le
      have h3 : 3 < KB + 1 := by exact_mod_cast h2
      omega
    -- `R₂^B = ⌊7(K^B − 1)/9⌋ + 1`
    set R₂ : ℕ := 7 * (KB - 1) / 9 + 1 with hR₂
    have hR2a : 7 * (KB - 1) < 9 * R₂ := by omega
    have hR2b : 9 * R₂ ≤ 7 * (KB - 1) + 9 := by omega
    -- `b₁ = ⌊L/2⌋`: `R₂ ≤ b₁ ≤ 12.9 K^B`
    have hb1le : ((L / 2 : ℕ) : ℝ) ≤ (L:ℝ) / 2 := Nat.cast_div_le
    have hb1ge : (L:ℝ) ≤ 2 * ((L / 2 : ℕ) : ℝ) + 1 := by
      have : L ≤ 2 * (L / 2) + 1 := by omega
      exact_mod_cast this
    have hLlo : q * ℓ2 ≤ (L:ℝ) * (1.6 * ℓ2) := by nlinarith only [hLl, hsl', hhl0, hl3b]
    have hLlo' : (q:ℝ) ≤ 1.6 * L := by
      have : (q:ℝ) * ℓ2 ≤ (1.6 * L) * ℓ2 := by linarith
      exact le_of_mul_le_mul_right this hl2p
    have hKBq' : (KB:ℝ) * ℓ2 ≤ q * ℓ2 / 21 := by nlinarith only [hKBa, hlogq, hl2p]
    have hKBq'' : (KB:ℝ) ≤ q / 21 := by
      have : (KB:ℝ) * ℓ2 ≤ (q / 21) * ℓ2 := by linarith
      exact le_of_mul_le_mul_right this hl2p
    have hR2r : 9 * (R₂:ℝ) ≤ 7 * KB + 2 := by
      have : 9 * R₂ ≤ 7 * KB + 2 := by omega
      exact_mod_cast this
    have hR2L : R₂ ≤ L / 2 := by
      have : (R₂:ℝ) ≤ ((L / 2 : ℕ) : ℝ) := by nlinarith only [hR2r, hKBq'', hb1ge, hLlo', hbig, hlogq]
      exact_mod_cast this
    have hb1pos : 1 ≤ L / 2 := by omega
    have hb1K : ((L / 2 : ℕ) : ℝ) ≤ 12.9 * KB := by
      have h1 : ((L / 2 : ℕ) : ℝ) * ℓ2 ≤ 0.61265 * (q * ℓ2) := by nlinarith only [hb1le, hLq, hl2p]
      have h2 : ((L / 2 : ℕ) : ℝ) * ℓ2 ≤ (12.9 * KB) * ℓ2 := by
        nlinarith only [h1, hKBb, hbig, hlogq, hX1, hl2b, hl2p]
      exact le_of_mul_le_mul_right h2 hl2p
    -- the height: `h(a₀/(3^e b₀)) ≤ log max(|a₀|, 3|b₀|) ≤ log 3 + D log 2 + W`
    set B : ℤ := 3 ^ (L % 2) * b0 with hB
    have hBle : |B| ≤ 3 * |b0| := by
      rw [hB, abs_mul, abs_pow]
      have : |(3:ℤ)| ^ (L % 2) ≤ 3 := by
        have : L % 2 ≤ 1 := by omega
        interval_cases (L % 2) <;> norm_num
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have hmaxM : max |(a0:ℝ)| |(B:ℝ)| ≤ 3 * (M:ℝ) := by
      have h1 : |(a0:ℝ)| ≤ (M:ℝ) := by rw [← Int.cast_abs]; exact_mod_cast hMa
      have h2 : |(B:ℝ)| ≤ 3 * (M:ℝ) := by
        rw [← Int.cast_abs]
        have : |B| ≤ 3 * M := le_trans hBle (by linarith)
        exact_mod_cast this
      have h0 : (0:ℝ) ≤ M := le_trans (abs_nonneg _) h1
      exact max_le (by linarith) h2
    have hmax1 : (1:ℝ) ≤ max |(a0:ℝ)| |(B:ℝ)| := by
      refine le_trans ?_ (le_max_left _ _)
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs ha0
    set Ht := logHt a0 B with hHt
    have hHt0 : 0 ≤ Ht := Real.log_nonneg hmax1
    have hHtle : Ht ≤ ℓ3 + D * ℓ2 + W := by
      have h1 : Ht ≤ Real.log (3 * (2 ^ D * H')) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hHpos.ne', hlogH] at h1
      linarith
    have hHtK : Ht ≤ 0.132 * KB := by
      have hA0 : 0 ≤ ℓ3 + ℓ2 + 2 * Real.log q := by linarith
      have h1 : Ht * ℓ2 ≤ (ℓ3 + ℓ2 + 2 * Real.log q) * ℓ2 + 0.00900001 * (q * ℓ2) * ℓ2 := by
        have : Ht ≤ ℓ3 + ℓ2 + 2 * Real.log q + 0.00900001 * (q * ℓ2) := by
          nlinarith only [hHtle, hDl, hWle, hhl]
        have := mul_le_mul_of_nonneg_right this hl2p.le
        linarith
      have h2 : (ℓ3 + ℓ2 + 2 * Real.log q) * ℓ2 ≤ (ℓ3 + ℓ2 + 2 * Real.log q) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hl2b.le hA0
      have h3 : (q * ℓ2) * ℓ2 ≤ (q * ℓ2) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hl2b.le (by positivity)
      have h4 : Ht * ℓ2 ≤ (0.132 * KB) * ℓ2 := by
        nlinarith only [h1, h2, h3, hKBb, hbig, hlogq, hX1, hl2b, hl3b, hl2p]
      exact le_of_mul_le_mul_right h4 hl2p
    -- checking (1) and applying Theorem 1
    have hc := hK0 KB R₂ (L / 2) Ht hKBK0 hR2a hR2b hb1pos hb1K hHt0 hHtK
    rw [← J1_logHt_nine] at hc
    have key := J1_bug hB1 L hL2 a0 b0 hao hbo h8 hN0 hEq KB R₂ hKB3 hR2a hR2L hc
    rw [← hN0def, ← hv] at key
    -- contradiction between `v ≤ 21K^B − 1` and `v > (1 − 10^{−8})q − 2 log₂ q − 1`
    have hvK : v + 1 ≤ 21 * KB := by omega
    have hvKr : ((v:ℝ) + 1) * ℓ2 ≤ 21 * (KB:ℝ) * ℓ2 := by
      have : (v:ℝ) + 1 ≤ 21 * (KB:ℝ) := by exact_mod_cast hvK
      exact mul_le_mul_of_nonneg_right this hl2p.le
    nlinarith only [hvKr, hKBa, hmainlog, hWle, hhl, hl2p]

/-- Proposition 13.2B from Theorem 1 stated with the heights in lowest terms (`Thm1G1Red 8`, equivalent to `Thm1G1 8` by `thm1G1_iff_red`). -/
theorem hgt_thm1_of_red (hB1 : Thm1G1Red 8) (cD : ℝ) (hcD0 : 0 < cD) (hcD1 : cD ≤ 9e-3) :
    ∃ q0 : ℕ, ∀ s q L : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 → 0 ≤ hL s L →
      hL s L ≤ 1e-8 * q →
      LatticeCond q L ⌊cD * q⌋₊ (q * 2 ^ ⌊cD * q⌋₊ * (q * (2:ℝ) ^ hL s L + 1)) :=
  hgt_thm1 ((thm1G1_iff_red 8).2 hB1) cD hcD0 hcD1

end Collatz.M1
