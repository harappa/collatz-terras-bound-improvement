import CollatzProof.M1.Thm1Defs
import CollatzProof.M1.S13

/-!
# Analytic parts of Proposition 13.2B (Proposition 15.5 of the paper): checking condition (1) of Theorem 1 of Bugeaud (2002)

Step 3 of §13.5.2 of version 3 of the proof manuscript (Section 15.4 of the paper). When Theorem 1 is applied with `m = 8`, `g = 1`, `x₁/y₁ = 9`, `b₂ = 1`,
`L^B = 7`, `R₁^B = 7`, `S₁^B = 1`, `S₂^B = 9`, then, if `K = K^B` is sufficiently large, `7(K − 1) < 9R₂ ≤ 7(K − 1) + 9`
(the property of `R₂ = ⌊7(K − 1)/9⌋ + 1`), `b₁ ≤ 12.9K` and `0 ≤ H ≤ 0.132K` (`H` is the height of `x₂/y₂`), the left-hand side of (1) is positive (`T1_cond1`).

Instead of the limit `M_∞ = 0.29065…` of the manuscript, we show (inside the proof), by coarse rational estimates, `(left-hand side of (1)) ≥ 0.145K − 4 log K − 55`:
- `log ∏_{k=1}^{K−1} k! ≥ Σ_{k=1}^{K−1}(k log k − k) ≥ (K−1)²/2 · log(K−1) − (K−1)²/4 − (K−1)K/2` (`T1_log_fact_ge`:
  `k^k/k! ≤ e^k`; `T1_sum_klogk`: an induction showing `G(n+1) − G(n) ≤ (n+1)log(n+1) − (n+1)` by `log(1 + 1/n) ≤ 1/n`).
  Lemma 4 on p. 145 of the original paper is not used.
- `(K − 1) log b ≤ (K − 1) log X − (K − 2) log(K − 1) + (3/2)(K − 1)` (`T1_log_bB_le`; `X = ((R − 1)b₂ + (S − 1)b₁)/2` is
  the first factor of `b`, here `X = ((R − 1) + 8b₁)/2 ≤ 54K`). Hence `(K − 1) log b ≤ (K − 1)(log 54 + 3/2) + 1 + log K`.
- `γ₁R = R/2 − 7K/54` and `63γ₂ ≤ 21.105` (`K ≥ 1000`).
- `log 3 < (8/5) log 2` (`3^5 < 2^8`, `J_log3_hi`) and `log 2 > 0.6931471803`.
-/

namespace Collatz.M1

open Bugeaud

/-! ## A lower bound for the logarithm of the product of factorials -/

/-- `k log k − k ≤ log k!` (`k^k/k! ≤ e^k`). -/
theorem T1_log_fact_ge (k : ℕ) : (k : ℝ) * Real.log k - k ≤ Real.log (k.factorial : ℕ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < (k.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos k
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) hk'.le k
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at h2
  linarith

/-- `Σ_{k=1}^{n}(k log k − k) ≥ n²/2 · log n − n²/4 − n(n+1)/2`. -/
theorem T1_sum_klogk (n : ℕ) :
    (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 - n * (n + 1) / 2 ≤
      ∑ k ∈ Finset.Icc 1 n, ((k : ℝ) * Real.log k - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have ha : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      have hab : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
        have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
        rw [e] at h1
        calc (n : ℝ) * Real.log (((n : ℝ) + 1) / n) ≤ n * (1 / n) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 1 := by field_simp
      have hab2 : (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ n := by
        have := mul_le_mul_of_nonneg_left hab (show (0 : ℝ) ≤ n by positivity)
        nlinarith
      nlinarith [ih, hab2, ha, hn1]

/-- `K(K − 2) log(K − 1) − (3/2)K(K − 1) ≤ 2 log ∏_{k=1}^{K−1} k!` (`K ≥ 2`). -/
theorem T1_logFactProd_ge (K : ℕ) (hK : 2 ≤ K) :
    (K : ℝ) * (((K : ℝ) - 2) * Real.log ((K : ℝ) - 1) - 3 / 2 * ((K : ℝ) - 1)) ≤
      2 * Real.log (factProd K) := by
  have hlog : Real.log (factProd K) =
      ∑ k ∈ Finset.Icc 1 (K - 1), Real.log ((k.factorial : ℕ) : ℝ) := by
    unfold factProd
    exact Real.log_prod (fun k _ => by exact_mod_cast (Nat.factorial_pos k).ne')
  have h1 : ∑ k ∈ Finset.Icc 1 (K - 1), ((k : ℝ) * Real.log k - k) ≤ Real.log (factProd K) := by
    rw [hlog]; exact Finset.sum_le_sum (fun k _ => T1_log_fact_ge k)
  have h2 := T1_sum_klogk (K - 1)
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  push_cast
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn
  rw [show (n : ℝ) + 1 - 1 = n by ring, show (n : ℝ) + 1 - 2 = n - 1 by ring]
  nlinarith [h1, h2, hl, hn]

/-- `(K − 1) log b = (K − 1) log X − (2/K) log ∏ k!` (`X = ((R − 1)b₂ + (S − 1)b₁)/2 > 0`, `K ≥ 2`). -/
theorem T1_log_bB {K R S b₁ b₂ : ℕ} (hK : 2 ≤ K)
    (hX : 0 < ((R : ℝ) - 1) * b₂ + ((S : ℝ) - 1) * b₁) :
    ((K : ℝ) - 1) * Real.log (bB K R S b₁ b₂) =
      ((K : ℝ) - 1) * Real.log ((((R : ℝ) - 1) * b₂ + ((S : ℝ) - 1) * b₁) / 2)
        - 2 / K * Real.log (factProd K) := by
  have hP := factProd_pos K
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  unfold bB
  rw [Real.log_mul (div_pos hX two_pos).ne' (Real.rpow_pos_of_pos hP _).ne', Real.log_rpow hP]
  have e : ((K : ℝ) ^ 2 - K) = K * (K - 1) := by ring
  rw [e]
  field_simp
  ring

/-- `(K − 1) log b ≤ (K − 1) log X − ((K − 2) log(K − 1) − (3/2)(K − 1))`. -/
theorem T1_log_bB_le {K R S b₁ b₂ : ℕ} (hK : 2 ≤ K)
    (hX : 0 < ((R : ℝ) - 1) * b₂ + ((S : ℝ) - 1) * b₁) :
    ((K : ℝ) - 1) * Real.log (bB K R S b₁ b₂) ≤
      ((K : ℝ) - 1) * Real.log ((((R : ℝ) - 1) * b₂ + ((S : ℝ) - 1) * b₁) / 2)
        - (((K : ℝ) - 2) * Real.log ((K : ℝ) - 1) - 3 / 2 * ((K : ℝ) - 1)) := by
  rw [T1_log_bB hK hX]
  have h := T1_logFactProd_ge K hK
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have e : 2 / (K : ℝ) * Real.log (factProd K) = 2 * Real.log (factProd K) / K := by ring
  have : ((K : ℝ) - 2) * Real.log ((K : ℝ) - 1) - 3 / 2 * ((K : ℝ) - 1) ≤
      2 * Real.log (factProd K) / K := by
    rw [le_div_iff₀ hK0]
    linarith
  linarith

/-! ## Checking condition (1) -/

/-- For sufficiently large `K`, `K ≥ 1000` and `log K ≤ K/100`. -/
theorem T1_ev : ∃ K0 : ℕ, ∀ K : ℕ, K0 ≤ K → (1000 : ℝ) ≤ K ∧ Real.log K ≤ 0.01 * K := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ 0.01 * x := by
    have := Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 0.01 by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx0] at hx
    exact (le_abs_self _).trans hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 1000 ≤ x := Filter.eventually_ge_atTop _
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (h1.and h2))
  exact ⟨K0, fun K hK => ⟨(hK0 K hK).2, (hK0 K hK).1⟩⟩

/-- `γ₁R = R/2 − 7K/54` (`g = 1`, `S = 9`, `N = 7K`). -/
theorem T1_gam1 (r k : ℝ) (hr : 0 < r) : gam1 1 r 9 (k * 7) * r = r / 2 - 7 * k / 54 := by
  have hr' : r ≠ 0 := hr.ne'
  have h1 : (r + 1 - 1) / (2 * r) * r = r / 2 := by
    rw [show r + 1 - 1 = r by ring, div_mul_eq_mul_div, mul_div_mul_right _ _ hr']
  have h2 : 1 * (k * 7) / (6 * r * (9 + 1 - 1)) * r = 7 * k / 54 := by
    rw [div_mul_eq_mul_div, show 1 * (k * 7) * r = (7 * k) * r by ring,
      show 6 * r * (9 + 1 - 1) = 54 * r by ring, mul_div_mul_right _ _ hr']
  unfold gam1
  rw [sub_mul, h1, h2]

/-- `γ₂ = 1/2 − 7K/(54R)` (`g = 1`, `S = 9`, `N = 7K`). -/
theorem T1_gam2 (r k : ℝ) : gam2 1 r 9 (k * 7) = 1 / 2 - 7 * k / (54 * r) := by
  unfold gam2
  rw [show r + 1 - 1 = r by ring]
  ring

/-- The left-hand side of (1) in our application, expanded (`m = 8`, `x₁/y₁ = 9`, `b₂ = 1`, `L^B = 7`, `R₁^B = 7`, `S₁^B = 1`, `S₂^B = 9`). -/
theorem T1_cond1_eq (K R₂ b₁ : ℕ) (H : ℝ) :
    cond1 8 (Real.log 9) H b₁ 1 K 7 7 R₂ 1 9 =
      (K : ℝ) * 6 * Real.log 8 - 3 * Real.log ((K : ℝ) * 7)
        - ((K : ℝ) - 1) * Real.log (bB K (R₂ + 6) 9 b₁ 1)
        - gam1 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) * 7 * ((R₂ : ℝ) + 6) * Real.log 9
        - gam2 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) * 7 * 9 * H := by
  unfold cond1
  rw [show 7 + R₂ - 1 = R₂ + 6 by omega, show (1 + 9 - 1 : ℕ) = 9 by norm_num, primeFactors_eight,
    Finset.card_singleton]
  push_cast
  ring

/-- **Checking (1)**: if `K` is sufficiently large, `7(K − 1) < 9R₂ ≤ 7(K − 1) + 9`, `1 ≤ b₁ ≤ 12.9K` and `0 ≤ H ≤ 0.132K`, then
the left-hand side of condition (1) of Theorem 1 in our application is positive. -/
theorem T1_cond1 : ∃ K0 : ℕ, ∀ (K R₂ b₁ : ℕ) (H : ℝ), K0 ≤ K →
    7 * (K - 1) < 9 * R₂ → 9 * R₂ ≤ 7 * (K - 1) + 9 → 1 ≤ b₁ → (b₁ : ℝ) ≤ 12.9 * K →
    0 ≤ H → H ≤ 0.132 * K →
    0 < cond1 8 (Real.log 9) H b₁ 1 K 7 7 R₂ 1 9 := by
  obtain ⟨K0, hK0⟩ := T1_ev
  refine ⟨K0, fun K R₂ b₁ H hK hR1 hR2 hb1 hb1K hH0 hHK => ?_⟩
  obtain ⟨hk1000, hlogk⟩ := hK0 K hK
  rw [T1_cond1_eq]
  have hK2 : 2 ≤ K := by exact_mod_cast (show (2 : ℝ) ≤ K by linarith only [hk1000])
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hl3b := J_log3_hi
  have hl3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl54 : Real.log 54 = Real.log 2 + 3 * Real.log 3 := by
    rw [show (54 : ℝ) = 2 * 3 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hl7 : Real.log 7 ≤ 3 * Real.log 2 := by
    rw [← hl8]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hk0 : (0 : ℝ) < K := by linarith only [hk1000]
  have hlogK7 : Real.log ((K : ℝ) * 7) = Real.log K + Real.log 7 :=
    Real.log_mul hk0.ne' (by norm_num)
  -- `R = R₂ + 6`
  have hRr1 : 7 * (K : ℝ) < 9 * (R₂ : ℝ) + 7 := by exact_mod_cast (show 7 * K < 9 * R₂ + 7 by omega)
  have hRr2 : 9 * (R₂ : ℝ) ≤ 7 * K + 2 := by exact_mod_cast (show 9 * R₂ ≤ 7 * K + 2 by omega)
  have hR0 : (0 : ℝ) ≤ R₂ := Nat.cast_nonneg _
  have hr6 : (0 : ℝ) < (R₂ : ℝ) + 6 := by linarith only [hR0]
  -- the term γ₁ L R h(9): `γ₁R = R/2 − 7K/54`
  have hg1 : gam1 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) * ((R₂ : ℝ) + 6) =
      ((R₂ : ℝ) + 6) / 2 - 7 * K / 54 := T1_gam1 _ _ hr6
  have hA : gam1 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) * 7 * ((R₂ : ℝ) + 6) * Real.log 9 ≤
      (49 * K / 27 + 196 / 9) * (2 * Real.log 3) := by
    have e : gam1 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) * 7 * ((R₂ : ℝ) + 6) * Real.log 9 =
        7 * (gam1 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) * ((R₂ : ℝ) + 6)) * (2 * Real.log 3) := by
      rw [hl9]; ring
    rw [e, hg1]
    have : 7 * (((R₂ : ℝ) + 6) / 2 - 7 * K / 54) ≤ 49 * K / 27 + 196 / 9 := by
      linarith only [hRr2]
    exact mul_le_mul_of_nonneg_right this (by linarith only [hl3p])
  -- the term γ₂ L S H: `63 γ₂ ≤ 21.105`
  have hg2 : gam2 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) = 1 / 2 - 7 * K / (54 * ((R₂ : ℝ) + 6)) :=
    T1_gam2 _ _
  have hg2le : gam2 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) ≤ 0.335 := by
    rw [hg2]
    have : 0.165 ≤ 7 * (K : ℝ) / (54 * ((R₂ : ℝ) + 6)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [hRr2, hk1000]
    linarith only [this]
  have hB : gam2 1 ((R₂ : ℝ) + 6) 9 ((K : ℝ) * 7) * 7 * 9 * H ≤ 0.335 * 63 * (0.132 * K) := by
    have h1 := mul_le_mul_of_nonneg_right hg2le hH0
    linarith only [h1, hHK]
  -- the term (K − 1) log b
  have hb1r : (1 : ℝ) ≤ b₁ := by exact_mod_cast hb1
  have hX : 0 < (((R₂ + 6 : ℕ) : ℝ) - 1) * ((1 : ℕ) : ℝ) + (((9 : ℕ) : ℝ) - 1) * b₁ := by
    push_cast; linarith only [hR0, hb1r]
  have hC0 := T1_log_bB_le hK2 hX
  have hXle : ((((R₂ + 6 : ℕ) : ℝ) - 1) * ((1 : ℕ) : ℝ) + (((9 : ℕ) : ℝ) - 1) * b₁) / 2 ≤
      54 * K := by
    push_cast; linarith only [hRr2, hb1K, hk1000]
  have hXpos : 0 < ((((R₂ + 6 : ℕ) : ℝ) - 1) * ((1 : ℕ) : ℝ) + (((9 : ℕ) : ℝ) - 1) * b₁) / 2 := by
    positivity
  have hlogX : Real.log (((((R₂ + 6 : ℕ) : ℝ) - 1) * ((1 : ℕ) : ℝ) + (((9 : ℕ) : ℝ) - 1) * b₁) / 2)
      ≤ Real.log 54 + Real.log K := by
    rw [← Real.log_mul (by norm_num) hk0.ne']
    exact Real.log_le_log hXpos hXle
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith only [hk1000]
  have hlogdiff : ((K : ℝ) - 1) * (Real.log K - Real.log ((K : ℝ) - 1)) ≤ 1 := by
    rw [← Real.log_div hk0.ne' hK1.ne']
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (K : ℝ) / ((K : ℝ) - 1) by positivity)
    have e : (K : ℝ) / ((K : ℝ) - 1) - 1 = 1 / ((K : ℝ) - 1) := by field_simp; ring
    rw [e] at h1
    calc ((K : ℝ) - 1) * Real.log ((K : ℝ) / ((K : ℝ) - 1)) ≤ ((K : ℝ) - 1) * (1 / ((K : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left h1 hK1.le
      _ = 1 := by field_simp
  have hlogK1 : Real.log ((K : ℝ) - 1) ≤ Real.log K :=
    Real.log_le_log hK1 (by linarith only [hk1000])
  have hC : ((K : ℝ) - 1) * Real.log (bB K (R₂ + 6) 9 b₁ 1) ≤
      ((K : ℝ) - 1) * (Real.log 2 + 3 * Real.log 3) + 1 + Real.log K + 3 / 2 * ((K : ℝ) - 1) := by
    have h1 := mul_le_mul_of_nonneg_left hlogX hK1.le
    rw [hl54] at h1
    linarith only [hC0, h1, hlogdiff, hlogK1]
  -- summing up: `≥ 0.145K − 4 log K − 55`
  have hk3 : (K : ℝ) * Real.log 3 ≤ 1.6 * ((K : ℝ) * Real.log 2) := by
    have := mul_le_mul_of_nonneg_left hl3b.le hk0.le
    linarith only [this]
  have hk2 : 0.6931471803 * (K : ℝ) ≤ (K : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hl2a.le hk0.le
    linarith only [this]
  rw [hl8, hlogK7]
  linarith only [hA, hB, hC, hk3, hk2, hl7, hlogk, hk1000, hl2a, hl2b, hl3p, hl3b]

end Collatz.M1
