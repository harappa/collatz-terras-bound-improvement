import CollatzProof.M1.DeepDefs

/-!
# Common results of §1–§2 (those used across sections)

Numerical estimates of the constants (§1.4, Appendix A.1), Lemma 1.2 (the form of words), Lemma 1.7, properties of `L_p`. The counting (§2) is in `Counting.lean`.
-/

namespace Collatz.M1

open Finset

/-! ## Constants (§1.4, Appendix A.1) -/

/-! ### Auxiliary (placed under `Basics` to avoid name clashes) -/

namespace Basics

/-- If `2^p D^q < N^q`, then `p/q < log₂(N/D)` (a lower bound for the logarithm of a rational, reduced to an integer comparison). -/
lemma lt_logb2_of_nat {p q N D : ℕ} (hq : 0 < q) (hD : 0 < D) (h : 2 ^ p * D ^ q < N ^ q) :
    (p : ℝ) / q < Real.logb 2 ((N : ℝ) / D) := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp [zero_pow hq.ne'] at h
    · exact h0
  have hy : (0:ℝ) < (N:ℝ) / D := by positivity
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) hy]
  apply lt_of_pow_lt_pow_left₀ q hy.le
  have e : ((2:ℝ) ^ ((p:ℝ) / q)) ^ q = 2 ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      div_mul_cancel₀ _ (by exact_mod_cast hq.ne')]
    exact Real.rpow_natCast 2 p
  rw [e, div_pow, lt_div_iff₀ (by positivity)]
  exact_mod_cast h

/-- If `N^q < 2^p D^q`, then `log₂(N/D) < p/q`. -/
lemma logb2_lt_of_nat {p q N D : ℕ} (hq : 0 < q) (hD : 0 < D) (hN : 0 < N)
    (h : N ^ q < 2 ^ p * D ^ q) : Real.logb 2 ((N : ℝ) / D) < (p : ℝ) / q := by
  have hy : (0:ℝ) < (N:ℝ) / D := by positivity
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hy]
  apply lt_of_pow_lt_pow_left₀ q (by positivity)
  have e : ((2:ℝ) ^ ((p:ℝ) / q)) ^ q = 2 ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      div_mul_cancel₀ _ (by exact_mod_cast hq.ne')]
    exact Real.rpow_natCast 2 p
  rw [e, div_pow, div_lt_iff₀ (by positivity)]
  exact_mod_cast h

/-- A precise interval for `λ`: `(1.584962, 1.584963)` (`2^{1584962} < 3^{10^6} < 2^{1584963}`). -/
theorem lam_fine : 1.584962 < lam ∧ lam < 1.584963 := by
  constructor
  · have := lt_logb2_of_nat (p := 1584962) (q := 1000000) (N := 3) (D := 1) (by norm_num)
      (by norm_num) (by
        set_option exponentiation.threshold 2000000 in decide)
    norm_num at this
    rw [lam]; norm_num; linarith
  · have := logb2_lt_of_nat (p := 1584963) (q := 1000000) (N := 3) (D := 1) (by norm_num)
      (by norm_num) (by norm_num) (by
        set_option exponentiation.threshold 2000000 in decide)
    norm_num at this
    rw [lam]; norm_num; linarith


lemma lam_pos : 0 < lam := by have := lam_fine; linarith
lemma aa_pos : 0 < aa := by have := lam_fine; unfold aa; linarith

/-- `log₂ λ ∈ (0.66444, 0.66445)`. -/
theorem logb_lam_fine : 0.66444 < Real.logb 2 lam ∧ Real.logb 2 lam < 0.66445 := by
  obtain ⟨h1, h2⟩ := lam_fine
  constructor
  · have := lt_logb2_of_nat (p := 66444) (q := 100000) (N := 1584962) (D := 1000000)
      (by norm_num) (by norm_num) (by
        set_option exponentiation.threshold 2000000 in decide)
    have hm : Real.logb 2 ((1584962:ℕ) / (1000000:ℕ) : ℝ) < Real.logb 2 lam :=
      Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num; linarith)
    norm_num at this hm ⊢; linarith
  · have := logb2_lt_of_nat (p := 66445) (q := 100000) (N := 1584963) (D := 1000000)
      (by norm_num) (by norm_num) (by norm_num) (by
        set_option exponentiation.threshold 2000000 in decide)
    have hm : Real.logb 2 lam < Real.logb 2 ((1584963:ℕ) / (1000000:ℕ) : ℝ) :=
      Real.logb_lt_logb (by norm_num) lam_pos (by norm_num; linarith)
    norm_num at this hm ⊢; linarith

/-- `log₂(1/a) ∈ (0.77358, 0.77359)`. -/
theorem logb_inv_aa_fine : 0.77358 < Real.logb 2 (1 / aa) ∧ Real.logb 2 (1 / aa) < 0.77359 := by
  obtain ⟨h1, h2⟩ := lam_fine
  have ha : 0 < aa := aa_pos
  constructor
  · have := lt_logb2_of_nat (p := 77358) (q := 100000) (N := 1000000) (D := 584963)
      (by norm_num) (by norm_num) (by
        set_option exponentiation.threshold 2000000 in decide)
    have hm : Real.logb 2 ((1000000:ℕ) / (584963:ℕ) : ℝ) < Real.logb 2 (1 / aa) := by
      apply Real.logb_lt_logb (by norm_num) (by norm_num)
      rw [lt_one_div (by norm_num) ha]; unfold aa; norm_num; linarith
    norm_num at this hm ⊢; linarith
  · have := logb2_lt_of_nat (p := 77359) (q := 100000) (N := 1000000) (D := 584962)
      (by norm_num) (by norm_num) (by norm_num) (by
        set_option exponentiation.threshold 2000000 in decide)
    have hm : Real.logb 2 (1 / aa) < Real.logb 2 ((1000000:ℕ) / (584962:ℕ) : ℝ) := by
      apply Real.logb_lt_logb (by norm_num) (by positivity)
      rw [one_div_lt ha (by norm_num)]; unfold aa; norm_num; linarith
    norm_num at this hm ⊢; linarith

/-- `c = 1 − log₂ λ − (a/λ) log₂(1/a)`. -/
lemma cc_eq : cc = 1 - Real.logb 2 lam - (aa / lam) * Real.logb 2 (1 / aa) := by
  have hl := lam_pos
  have ha := aa_pos
  have h1 : 1 - 1 / lam = aa / lam := by unfold aa; field_simp
  have e1 : Real.logb 2 (1 / lam) = -Real.logb 2 lam := by rw [one_div, Real.logb_inv]
  have e2 : Real.logb 2 (aa / lam) = -Real.logb 2 (1 / aa) - Real.logb 2 lam := by
    rw [Real.logb_div ha.ne' hl.ne', one_div, Real.logb_inv]; ring
  unfold cc Hb rhoc
  rw [h1, e1, e2]
  have : aa = lam - 1 := rfl
  field_simp
  rw [this]; ring

end Basics

open Basics

theorem lam_bounds : 1.5849 < lam ∧ lam < 1.585 := by
  obtain ⟨h1, h2⟩ := lam_fine; constructor <;> linarith

theorem rhoc_bounds : 0.6309 < rhoc ∧ rhoc < 0.631 := by
  obtain ⟨h1, h2⟩ := lam_fine
  have hl := lam_pos
  unfold rhoc
  constructor
  · rw [lt_div_iff₀ hl]; nlinarith
  · rw [div_lt_iff₀ hl]; nlinarith

theorem cc_bounds : 0.05 < cc ∧ cc < 0.0501 := by
  obtain ⟨h1, h2⟩ := lam_fine
  obtain ⟨l1, l2⟩ := logb_lam_fine
  obtain ⟨m1, m2⟩ := logb_inv_aa_fine
  have hl := lam_pos
  rw [cc_eq]
  have ea : aa / lam = 1 - 1 / lam := by unfold aa; field_simp
  rw [ea]
  have r1 : 1 / lam < 1 / 1.584962 := one_div_lt_one_div_of_lt (by norm_num) h1
  have r2 : 1 / 1.584963 < 1 / lam := one_div_lt_one_div_of_lt hl h2
  generalize 1 / lam = u at r1 r2 ⊢
  generalize Real.logb 2 (1 / aa) = v at m1 m2 ⊢
  norm_num at r1 r2
  constructor
  · nlinarith [mul_pos (sub_pos.2 r2) (sub_pos.2 m2), mul_pos (sub_pos.2 r2) (sub_pos.2 m1)]
  · nlinarith [mul_pos (sub_pos.2 r1) (sub_pos.2 m1), mul_pos (sub_pos.2 r1) (sub_pos.2 m2)]

theorem tstar_bounds : 0.488 < tstar ∧ tstar < 0.4881 := by
  obtain ⟨h1, h2⟩ := lam_fine
  obtain ⟨m1, m2⟩ := logb_inv_aa_fine
  have hl := lam_pos
  unfold tstar
  constructor
  · rw [lt_div_iff₀ hl]; nlinarith
  · rw [div_lt_iff₀ hl]; nlinarith

theorem rc_bounds : 0.9651 < rc ∧ rc < 0.9652 := by
  obtain ⟨h1, h2⟩ := lam_fine
  have hl := lam_pos
  have eX : rhoc * (1 - rhoc) = (lam - 1) / lam ^ 2 := by unfold rhoc; field_simp
  unfold rc
  rw [eX]
  constructor
  · have : (0.48255:ℝ) < Real.sqrt ((lam - 1) / lam ^ 2) := by
      rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ (by positivity)]
      nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]
    linarith
  · have : Real.sqrt ((lam - 1) / lam ^ 2) < 0.4826 := by
      rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]
    linarith


/-- Lemma 1.7: `m(t*) = (2^{t*a} + 2^{−t*})/2 = f = 2^{−c}`, `ρ_c = 2^{t*a}/(2f)`, `1 − ρ_c = 2^{−t*}/(2f)`. -/
theorem lemma17 :
    ((2:ℝ) ^ (tstar * aa) + (2:ℝ) ^ (-tstar)) / 2 = ff ∧
    rhoc = (2:ℝ) ^ (tstar * aa) / (2 * ff) ∧ 1 - rhoc = (2:ℝ) ^ (-tstar) / (2 * ff) := by
  have hl := lam_pos
  have ha := aa_pos
  have hla : lam = 1 + aa := by unfold aa; ring
  set v := Real.logb 2 (1 / aa) with hv
  set w := Real.logb 2 lam with hw
  have h2v : (2:ℝ) ^ v = 1 / aa := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  have h2w : (2:ℝ) ^ w = lam := Real.rpow_logb (by norm_num) (by norm_num) hl
  have ht : tstar = v / lam := rfl
  set Y := (2:ℝ) ^ (tstar * aa) with hY
  have hYpos : 0 < Y := by positivity
  -- `2^{−t*} = a · 2^{t* a}`
  have hX : (2:ℝ) ^ (-tstar) = aa * Y := by
    have e : -tstar = tstar * aa - v := by rw [ht]; field_simp; rw [hla]; ring
    rw [e, Real.rpow_sub (by norm_num), h2v, hY]; field_simp
  -- `f = λ 2^{t* a} / 2`
  have hf : ff = lam * Y / 2 := by
    have e : -cc = w + tstar * aa - 1 := by rw [cc_eq, ht]; ring
    rw [ff, e, Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num), h2w, hY]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hX, hf, hla]; ring
  · rw [hf]; unfold rhoc; field_simp
  · rw [hX, hf]; unfold rhoc; field_simp; rw [hla]; ring

/-! ## Words and Terras numbers (Lemmas 1.1, 1.2) -/

theorem mOf_lt {n : ℕ} (x : Fin n → Bool) : mOf x < 2 ^ n := ((terrasEquiv n).symm x).2

theorem pw_mOf {n : ℕ} (x : Fin n → Bool) : pw (mOf x) n = x :=
  (terrasEquiv n).apply_symm_apply x

namespace Basics

/-- `o_j(m)` is the number of odd times among the first `j` steps. -/
lemma o_eq_card (m j : ℕ) : o m j = ((range j).filter (fun i => T^[i] m % 2 = 1)).card := by
  induction j with
  | zero => simp [o]
  | succ j ih =>
    rw [range_add_one, filter_insert]
    simp only [o, ih]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
    · simp

/-- `ones (pw m n) j = o_j(m)` (`j ≤ n`). -/
lemma ones_pw (m n j : ℕ) (hj : j ≤ n) : ones (pw m n) j = o m j := by
  rw [o_eq_card, ones]
  apply card_bij (fun (i : Fin n) _ => (i : ℕ))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and, pw, decide_eq_true_eq] at hi
    simp [hi.1, hi.2]
  · intro a _ b _ h; exact Fin.ext h
  · intro b hb
    simp only [mem_filter, mem_range] at hb
    exact ⟨⟨b, by omega⟩, by simp [pw, hb.1, hb.2], rfl⟩

lemma ones_eq_o {n : ℕ} (x : Fin n → Bool) : ones x n = o (mOf x) n := by
  conv_lhs => rw [← pw_mOf x]
  exact ones_pw _ _ _ le_rfl

end Basics

/-- Lemma 1.2 (i): `2^n a_x = 3^{|x|} m_x + c_x`. -/
theorem dual_word {n : ℕ} (x : Fin n → Bool) : 2 ^ n * aOf x = 3 ^ (ones x n) * mOf x + cOf x := by
  rw [ones_eq_o]; exact dual _ _

namespace Basics

/-- `o_{j+1}(m) = [m odd] + o_j(T m)`. -/
lemma o_succ_shift (m j : ℕ) : o m (j + 1) = (if m % 2 = 1 then 1 else 0) + o (T m) j := by
  induction j with
  | zero => by_cases h : m % 2 = 1 <;> simp [o, h]
  | succ j ih =>
    rw [o, ih, o, Function.iterate_succ_apply]; ring

/-- If `m < k 2^n`, then `T^n(m) < k 3^{o_n(m)}`. -/
lemma iter_lt_mul (n : ℕ) : ∀ m k : ℕ, m < k * 2 ^ n → T^[n] m < k * 3 ^ (o m n) := by
  induction n with
  | zero => intro m k h; simpa [o] using h
  | succ n ih =>
    intro m k h
    have hP : k * 2 ^ (n + 1) = 2 * (k * 2 ^ n) := by ring
    rw [hP] at h
    rw [Function.iterate_succ_apply, o_succ_shift]
    by_cases hm : m % 2 = 1
    · have hT : T m = (3 * m + 1) / 2 := by unfold T; simp [hm]
      have h3 : 3 * k * 2 ^ n = 3 * (k * 2 ^ n) := by ring
      have := ih (T m) (3 * k) (by rw [hT, h3]; omega)
      simp only [hm, ite_true]
      calc T^[n] (T m) < 3 * k * 3 ^ o (T m) n := this
        _ = k * 3 ^ (1 + o (T m) n) := by ring
    · have hm0 : m % 2 = 0 := by omega
      have hT : T m = m / 2 := by unfold T; simp [hm0]
      have := ih (T m) k (by rw [hT]; omega)
      simpa [hm] using this

end Basics

/-- Lemma 1.2 (ii): `0 ≤ a_x < 3^{|x|}`. -/
theorem aOf_lt {n : ℕ} (x : Fin n → Bool) : aOf x < 3 ^ (ones x n) := by
  rw [ones_eq_o, aOf]
  have := iter_lt_mul n (mOf x) 1 (by simpa using mOf_lt x)
  simpa using this

/-- Basic properties of `L_p`: `3^{L_p} ≤ 2^q < 3^{L_p+1}` (and `L_p ≥ 1` for `q ≥ 2`). -/
theorem Lp_spec (q : ℕ) : 3 ^ Lp q ≤ 2 ^ q ∧ 2 ^ q < 3 ^ (Lp q + 1) := by
  refine ⟨Nat.findGreatest_spec (P := fun l => 3 ^ l ≤ 2 ^ q) (Nat.zero_le q) (by simp [Nat.one_le_two_pow]), ?_⟩
  by_cases h : Lp q + 1 ≤ q
  · have := Nat.findGreatest_is_greatest (P := fun l => 3 ^ l ≤ 2 ^ q) (Nat.lt_succ_self _) h
    simpa [Lp] using this
  · have hle : Lp q ≤ q := Nat.findGreatest_le q
    have : Lp q = q := by omega
    rw [this]
    calc 2 ^ q < 3 ^ q * 3 := by
          have := Nat.pow_le_pow_left (show 2 ≤ 3 by norm_num) q
          have : 0 < 3 ^ q := by positivity
          omega
      _ = 3 ^ (q + 1) := by ring

end Collatz.M1
