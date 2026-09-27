import CollatzProof.M1.Sigma

/-!
# Specification tests for the statements of the formalization

We check that the definitions occurring in the statements of the main theorems `m1_main`, `sigma_main`, `divergent_count`
(`T`, `pw`, `ones`, `lam`, `hw`, `SurvW`, `NKcount`, `SigmaGt`, `SigmaCount`, `DivCount`) have the meaning of the manuscript
(`𝒩_K` of Definition 1.3, the stopping time `σ` of §14.5). The inequalities of the main theorems cannot be tested on small values (they are asymptotic), so we test the definitions.
1. The real-valued survival condition in integer form (proved): `SurvW 0 (pw n K)` (height `λ o_j − j ≥ 0`) ⟺ for all
   `1 ≤ j ≤ K`, `2^j ≤ 3^{o_j}` (the coefficient `3^{o_j}/2^j` is at least 1, i.e. the coefficient stopping time exceeds `K`).
   `ones (pw n K) j` is the number `o_j(n)` of odd terms among `n, T(n), …, T^{j−1}(n)`.
2. Decidable forms of `NKcount` and `SigmaCount` (proved), and their values at small `(K, X)` (by `decide`).
3. `DivCount`: `n = 1` is counted (the cycle `T 1 = 2`, `T 2 = 1` gives `σ(1) = ∞`). `1 ≤ DivCount X` for `X ≥ 1`, and
   `DivCount 100 = 1`.
4. Individual values (`T 27 = 41`, `pw 27 5`, the coefficient stopping time and the stopping time of 27 are both 59) and the reading of `⌊2^{αK}⌋₊` in the main theorems.
The values agree with the output of `audit/m1_spec.py` of the source repository (a brute force independent of Lean, standard library only):
`NKcount 5 40 = 5`, `NKcount 8 100 = 6`, `NKcount 10 200 = 13`, `NKcount 12 300 = 19`; `SigmaCount` is respectively
6, 7, 14, 20 (the difference is `n = 1`); `DivCount 100 = 1`.
Only `decide` and `rfl` are used (every computation is checked by the kernel; no decision procedure that trusts compiled evaluation is used).
-/

namespace Collatz.M1

open Finset

set_option maxRecDepth 100000

/-! ## 1. The survival condition is an integer condition -/

/-- `0 ≤ λ a − j ⟺ 2^j ≤ 3^a` (`λ = log₂ 3`), from `2^{λ a} = 3^a` and the monotonicity of `x ↦ 2^x`. -/
theorem spec_lam_sub_nonneg_iff (a j : ℕ) : (0:ℝ) ≤ lam * a - j ↔ 2 ^ j ≤ 3 ^ a := by
  have h2 : (2:ℝ) ^ (lam * a) = 3 ^ a := by
    rw [Real.rpow_mul (by norm_num), lam, Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_natCast]
  rw [sub_nonneg, ← Real.rpow_le_rpow_left_iff (show (1:ℝ) < 2 by norm_num), h2, Real.rpow_natCast]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- **Spec 1**: `n ∈ 𝒩_K` (`SurvW 0 (pw n K)`: the real height `λ o_j − j` is nonnegative for `1 ≤ j ≤ K`) ⟺
`2^j ≤ 3^{o_j}` for all `1 ≤ j ≤ K` (Definition 1.3 of the manuscript; the coefficient stopping time exceeds `K`). -/
theorem spec_survW_iff (n K : ℕ) :
    SurvW 0 (pw n K) ↔ ∀ j, 1 ≤ j → j ≤ K → 2 ^ j ≤ 3 ^ ones (pw n K) j := by
  unfold SurvW hw
  simp only [zero_add, spec_lam_sub_nonneg_iff]

/-- Finite form of Spec 1 (the form passed to `decide`). -/
theorem spec_survW_iff_Icc (n K : ℕ) :
    SurvW 0 (pw n K) ↔ ∀ j ∈ Icc 1 K, 2 ^ j ≤ 3 ^ ones (pw n K) j := by
  rw [spec_survW_iff]
  constructor
  · intro h j hj; rw [mem_Icc] at hj; exact h j hj.1 hj.2
  · intro h j h1 h2; exact h j (mem_Icc.2 ⟨h1, h2⟩)

/-- For `j ≤ K`, `ones (pw n K) j` is the number of odd terms among `n, T(n), …, T^{j−1}(n)` (`o_j(n)` of the manuscript). -/
theorem spec_ones_pw (n K j : ℕ) (hj : j ≤ K) :
    ones (pw n K) j = ((range j).filter (fun i => T^[i] n % 2 = 1)).card := by
  rw [K_ones_pw n K j hj, K_o_eq_sum, card_filter]

/-! ## 2. Decidable forms of `NKcount` and `SigmaCount`, and small values -/

/-- Decidable form of `NKcount`: `#{1 ≤ n ≤ X : 2^j ≤ 3^{o_j} for all 1 ≤ j ≤ K}`. -/
def NKcountZ (K X : ℕ) : ℕ :=
  ((Icc 1 X).filter (fun n => ∀ j ∈ Icc 1 K, 2 ^ j ≤ 3 ^ ones (pw n K) j)).card

/-- **Spec 2**: `NKcount K X = NKcountZ K X`. -/
theorem spec_NKcount_eq (K X : ℕ) : NKcount K X = NKcountZ K X := by
  classical
  unfold NKcount NKcountZ
  congr 1
  exact filter_congr (fun n _ => spec_survW_iff_Icc n K)

/-- Decidable form of `SigmaCount`: `#{1 ≤ n ≤ X : n ≤ T^j(n) for all 1 ≤ j ≤ K}`. -/
def SigmaCountZ (K X : ℕ) : ℕ :=
  ((Icc 1 X).filter (fun n : ℕ => ∀ j ∈ (Icc 1 K : Finset ℕ), n ≤ T^[j] n)).card

/-- Finite form of `SigmaGt n K` (`σ(n) > K`). -/
theorem spec_sigmaGt_iff_Icc (n K : ℕ) : SigmaGt n K ↔ ∀ j ∈ (Icc 1 K : Finset ℕ), n ≤ T^[j] n := by
  constructor
  · intro h j hj; rw [mem_Icc] at hj; exact h j hj.1 hj.2
  · intro h j h1 h2; exact h j (mem_Icc.2 ⟨h1, h2⟩)

/-- **Spec 3**: `SigmaCount K X = SigmaCountZ K X`. -/
theorem spec_SigmaCount_eq (K X : ℕ) : SigmaCount K X = SigmaCountZ K X := by
  classical
  unfold SigmaCount SigmaCountZ
  congr 1
  exact filter_congr (fun n _ => spec_sigmaGt_iff_Icc n K)

-- `𝒩_5 ∩ [1, 40] = {7, 15, 27, 31, 39}` and `{1 ≤ n ≤ 40 : σ(n) > 5} = {1, 7, 15, 27, 31, 39}`
theorem spec_NK_5_40_set :
    (Icc 1 40).filter (fun n => ∀ j ∈ Icc 1 5, 2 ^ j ≤ 3 ^ ones (pw n 5) j) = {7, 15, 27, 31, 39} := by
  decide

theorem spec_sigma_5_40_set :
    (Icc 1 40).filter (fun n : ℕ => ∀ j ∈ (Icc 1 5 : Finset ℕ), n ≤ T^[j] n) = {1, 7, 15, 27, 31, 39} := by
  decide

-- Counts (the same as the brute force of `audit/m1_spec.py`)
theorem spec_NKcount_5_40 : NKcount 5 40 = 5 := by rw [spec_NKcount_eq]; decide
theorem spec_NKcount_8_100 : NKcount 8 100 = 6 := by rw [spec_NKcount_eq]; decide
theorem spec_NKcount_10_200 : NKcount 10 200 = 13 := by rw [spec_NKcount_eq]; decide
theorem spec_SigmaCount_5_40 : SigmaCount 5 40 = 6 := by rw [spec_SigmaCount_eq]; decide
theorem spec_SigmaCount_8_100 : SigmaCount 8 100 = 7 := by rw [spec_SigmaCount_eq]; decide
theorem spec_SigmaCount_10_200 : SigmaCount 10 200 = 14 := by rw [spec_SigmaCount_eq]; decide
theorem spec_NKcount_12_300 : NKcount 12 300 = 19 := by rw [spec_NKcount_eq]; decide
theorem spec_SigmaCount_12_300 : SigmaCount 12 300 = 20 := by rw [spec_SigmaCount_eq]; decide
-- `K = 0`: the condition is empty, and every `n ∈ [1, X]` is counted
theorem spec_NKcount_0_10 : NKcount 0 10 = 10 := by rw [spec_NKcount_eq]; decide

/-! ## 3. `DivCount`: `σ(1) = ∞` -/

lemma spec_T_pos {n : ℕ} (hn : 0 < n) : 0 < T n := by
  unfold T; split_ifs <;> omega

lemma spec_iterate_T_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < T^[j] n := by
  induction j with
  | zero => simpa using hn
  | succ j ih => rw [Function.iterate_succ_apply']; exact spec_T_pos ih

/-- `σ(1) = ∞`: `SigmaGt 1 K` for every `K` (the orbit is 1, 2, 1, 2, …). -/
theorem spec_sigmaGt_one (K : ℕ) : SigmaGt 1 K := fun j _ _ => spec_iterate_T_pos one_pos j

/-- **Spec 4**: `DivCount X ≥ 1` for `X ≥ 1` (`n = 1` is counted). -/
theorem spec_one_le_DivCount {X : ℕ} (hX : 1 ≤ X) : 1 ≤ DivCount X := by
  classical
  unfold DivCount
  have : 0 < ((Icc 1 X).filter (fun n => ∀ K, SigmaGt n K)).card :=
    card_pos.2 ⟨1, mem_filter.2 ⟨mem_Icc.2 ⟨le_rfl, hX⟩, spec_sigmaGt_one⟩⟩
  exact this

/-- **Spec 5**: `DivCount 100 = 1` (every `2 ≤ n ≤ 100` drops below `n` within `59` steps; the maximum, 59, is attained at `n = 27`). -/
theorem spec_DivCount_100 : DivCount 100 = 1 := by
  classical
  have hstop : ∀ n ∈ Icc 2 100, ∃ j ∈ Icc 1 59, T^[j] n < n := by decide
  unfold DivCount
  rw [card_eq_one]
  refine ⟨1, ?_⟩
  ext n
  simp only [mem_filter, mem_Icc, mem_singleton]
  constructor
  · rintro ⟨⟨h1, h100⟩, hK⟩
    by_contra hne
    obtain ⟨j, hj, hlt⟩ := hstop n (mem_Icc.2 ⟨by omega, h100⟩)
    rw [mem_Icc] at hj
    have := hK j j hj.1 le_rfl
    omega
  · rintro rfl
    exact ⟨⟨le_rfl, by norm_num⟩, spec_sigmaGt_one⟩

/-! ## 4. Individual values, and `⌊2^{αK}⌋₊` in the main theorems -/

theorem spec_T_27 : T 27 = 41 := by decide
theorem spec_T_1_2 : T 1 = 2 ∧ T 2 = 1 := by decide
/-- The parities of 27, 41, 62, 31, 47 (`true` means odd). -/
theorem spec_pw_27_5 : pw 27 5 = ![true, true, false, true, true] := by decide
theorem spec_ones_27_5 : ones (pw 27 5) 5 = 4 := by decide

/-- `κ_coef(1) = 2`: `1 ∈ 𝒩_1` (`2 ≤ 3`) and `1 ∉ 𝒩_2` (`4 > 3`), whereas `σ(1) = ∞`. -/
theorem spec_one_mem_N1 : SurvW 0 (pw 1 1) := (spec_survW_iff_Icc 1 1).2 (by decide)
theorem spec_one_not_mem_N2 : ¬ SurvW 0 (pw 1 2) := by rw [spec_survW_iff_Icc]; decide

/-- The coefficient stopping time of 27 is 59: `27 ∈ 𝒩_58` and `27 ∉ 𝒩_59`. -/
theorem spec_27_mem_N58 : SurvW 0 (pw 27 58) := (spec_survW_iff_Icc 27 58).2 (by decide)
theorem spec_27_not_mem_N59 : ¬ SurvW 0 (pw 27 59) := by rw [spec_survW_iff_Icc]; decide

/-- The stopping time of 27 is 59: `σ(27) > 58` and `σ(27) ≤ 59`. -/
theorem spec_sigma_27 : SigmaGt 27 58 ∧ ¬ SigmaGt 27 59 := by
  rw [spec_sigmaGt_iff_Icc, spec_sigmaGt_iff_Icc]; decide

/-- `X = ⌊x⌋₊` in the main theorems (`x = 2^{αK} ≥ 0`): `n ∈ [1, ⌊x⌋₊] ⟺ 1 ≤ n ∧ n ≤ x`, so the integers `1 ≤ n ≤ 2^{αK}` are counted. -/
theorem spec_mem_Icc_floor {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : n ∈ Icc 1 ⌊x⌋₊ ↔ 1 ≤ n ∧ (n:ℝ) ≤ x := by
  rw [mem_Icc, Nat.le_floor_iff hx]

/-- Constants: `λ = log₂ 3 ∈ (1.584962, 1.584963)` and `c = 1 − H(1/λ) ∈ (0.05, 0.0501)` (restating theorems of `Basics.lean`). -/
theorem spec_constants : (1.584962 < lam ∧ lam < 1.584963) ∧ (0.05 < cc ∧ cc < 0.0501) :=
  ⟨Basics.lam_fine, cc_bounds⟩

end Collatz.M1
