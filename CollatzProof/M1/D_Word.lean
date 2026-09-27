import CollatzProof.M1.Counting

/-!
# Auxiliary results for Theorem B: combinatorics of words

The recursion for the number of 1s, the swap `flipU` of swap blocks, the closed form of `c_x` and its change under the swap (the combinatorial part of Lemma 5.3 (i)(ii)).
The prefix `D_` marks auxiliary declarations for Theorem B.
-/

namespace Collatz.M1

open Finset

/-! ## Extension of words to `ℕ` and the number of 1s -/

/-- Extension of a word to `ℕ` (`false` outside the range). -/
def D_xb {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then x ⟨i, h⟩ else false

lemma D_xb_of_ge {n : ℕ} (x : Fin n → Bool) {i : ℕ} (h : n ≤ i) : D_xb x i = false := by
  simp [D_xb, not_lt.mpr h]

lemma D_xb_fin {n : ℕ} (x : Fin n → Bool) (i : Fin n) : D_xb x i = x i := by
  simp [D_xb, i.2]

lemma D_xb_lt {n : ℕ} (x : Fin n → Bool) {i : ℕ} (h : i < n) : D_xb x i = x ⟨i, h⟩ := by
  simp [D_xb, h]

lemma D_ones_zero {n : ℕ} (x : Fin n → Bool) : ones x 0 = 0 := by
  simp [ones]

lemma D_ones_succ {n : ℕ} (x : Fin n → Bool) (j : ℕ) :
    ones x (j + 1) = ones x j + (if D_xb x j then 1 else 0) := by
  classical
  unfold ones
  rw [card_filter, card_filter]
  have h1 : ∀ i : Fin n, (if ((i : ℕ) < j + 1 ∧ x i = true) then 1 else 0) =
      (if ((i : ℕ) < j ∧ x i = true) then 1 else 0) + (if ((i : ℕ) = j ∧ x i = true) then 1 else 0) := by
    intro i
    by_cases hx : x i = true
    · simp only [hx, and_true]; split_ifs <;> omega
    · simp [hx]
  rw [sum_congr rfl (fun i _ => h1 i), sum_add_distrib]
  congr 1
  by_cases h : j < n
  · rw [D_xb_lt x h, sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ j := fun e => hb (Fin.ext e)
      simp [this]
    · simp
  · rw [D_xb_of_ge x (by omega)]
    apply sum_eq_zero
    intro i _
    have : (i : ℕ) ≠ j := by have := i.2; omega
    simp [this]

lemma D_ones_mono {n : ℕ} (x : Fin n → Bool) {i j : ℕ} (h : i ≤ j) : ones x i ≤ ones x j := by
  induction j with
  | zero => simp_all
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · rw [D_ones_succ]; have := ih (by omega); omega
    · rw [show i = j + 1 by omega]

lemma D_ones_of_ge {n : ℕ} (x : Fin n → Bool) {j : ℕ} (h : n ≤ j) : ones x j = ones x n := by
  induction j with
  | zero => have : n = 0 := by omega
            subst this; rfl
  | succ j ih =>
    rcases Nat.lt_or_ge n (j + 1) with h' | h'
    · rw [D_ones_succ, ih (by omega), D_xb_of_ge x (by omega)]; simp
    · have : n = j + 1 := by omega
      subst this; rfl

/-! ## Swapping swap blocks -/

/-- Swapping the contents of the blocks in `U`: the block index of a position `i ≥ 1` is `(i+1)/2` (positions `2k−1, 2k` form block `k`).
On a block containing exactly one 1, flipping both letters is the swap `10 ↔ 01`. -/
def D_flipU {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) : Fin t → Bool :=
  fun i => if 1 ≤ (i : ℕ) ∧ ((i : ℕ) + 1) / 2 ∈ U then !τ i else τ i

lemma D_flipU_invol {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) : D_flipU U (D_flipU U τ) = τ := by
  funext i; unfold D_flipU; split_ifs <;> simp

lemma D_xb_flipU {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (i : ℕ) :
    D_xb (D_flipU U τ) i = if i < t ∧ 1 ≤ i ∧ (i + 1) / 2 ∈ U then !D_xb τ i else D_xb τ i := by
  unfold D_xb D_flipU
  by_cases h : i < t
  · simp only [h, dite_true, true_and]
  · simp [h]

/-- Every block of `U` is complete (`2k < t`) and contains exactly one 1. -/
def D_GoodU {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) : Prop :=
  ∀ k ∈ U, 1 ≤ k ∧ 2 * k < t ∧ D_xb τ (2 * k - 1) ≠ D_xb τ (2 * k)

/-- The number of 1s up to an odd position does not change under the swap. -/
lemma D_ones_flip_odd {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (hU : D_GoodU U τ) (m : ℕ) :
    ones (D_flipU U τ) (2 * m + 1) = ones τ (2 * m + 1) := by
  induction m with
  | zero =>
    simp only [mul_zero, zero_add]
    rw [D_ones_succ, D_ones_succ, D_ones_zero, D_ones_zero, D_xb_flipU]
    simp
  | succ m ih =>
    have e : ∀ x : Fin t → Bool, ones x (2 * (m + 1) + 1) = ones x (2 * m + 1) +
        (if D_xb x (2 * m + 1) then 1 else 0) + (if D_xb x (2 * m + 2) then 1 else 0) := by
      intro x
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring, D_ones_succ,
        show 2 * m + 2 = (2 * m + 1) + 1 by ring, D_ones_succ]
    rw [e, e, ih, D_xb_flipU, D_xb_flipU]
    have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have e2 : (2 * m + 2 + 1) / 2 = m + 1 := by omega
    rw [e1, e2]
    by_cases hk : m + 1 ∈ U
    · obtain ⟨_, hk2, hk3⟩ := hU _ hk
      have hlt1 : 2 * m + 1 < t := by omega
      have hlt2 : 2 * m + 2 < t := by omega
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) = 2 * m + 2 by ring] at hk3
      simp only [hlt1, hlt2, hk, show 1 ≤ 2 * m + 1 from by omega,
        show 1 ≤ 2 * m + 2 from by omega, and_self, ite_true]
      revert hk3
      cases D_xb τ (2 * m + 1) <;> cases D_xb τ (2 * m + 2) <;> simp
    · simp [hk]

lemma D_ones_flip_odd' {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (hU : D_GoodU U τ) {j : ℕ}
    (hj : j % 2 = 1) : ones (D_flipU U τ) j = ones τ j := by
  have := D_ones_flip_odd U τ hU (j / 2)
  rwa [show 2 * (j / 2) + 1 = j by omega] at this

/-- The number of 1s up to position `2k−1` (`k ≥ 1`) or `0` does not change. -/
lemma D_ones_flip_blockstart {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (hU : D_GoodU U τ) (k : ℕ) :
    ones (D_flipU U τ) (2 * k - 1) = ones τ (2 * k - 1) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp [D_ones_zero]
  · exact D_ones_flip_odd' U τ hU (by omega)

/-- At an even position `2k` with `k ∉ U`, the number of 1s does not change. -/
lemma D_ones_flip_even {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (hU : D_GoodU U τ) (k : ℕ)
    (hk : k ∉ U) : ones (D_flipU U τ) (2 * k) = ones τ (2 * k) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp [D_ones_zero]
  · rw [show 2 * k = (2 * k - 1) + 1 by omega, D_ones_succ, D_ones_succ,
      D_ones_flip_blockstart U τ hU k, D_xb_flipU]
    rw [show (2 * k - 1 + 1) / 2 = k by omega]
    simp [hk]

/-- Unless `j` is "an even position `2k` with `k ∈ U`", the number of 1s does not change. -/
lemma D_ones_flip_eq {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (hU : D_GoodU U τ) (j : ℕ)
    (hj : ¬ (j % 2 = 0 ∧ j / 2 ∈ U)) : ones (D_flipU U τ) j = ones τ j := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have hk : j / 2 ∉ U := fun e => hj ⟨h, e⟩
    have := D_ones_flip_even U τ hU (j / 2) hk
    rwa [show 2 * (j / 2) = j by omega] at this
  · exact D_ones_flip_odd' U τ hU h

/-- The total number of 1s does not change. -/
lemma D_ones_flip_total {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) (hU : D_GoodU U τ) :
    ones (D_flipU U τ) t = ones τ t := by
  apply D_ones_flip_eq U τ hU
  rintro ⟨h1, h2⟩
  have := (hU _ h2).2.1
  omega

lemma D_GoodU_mono {t : ℕ} {U V : Finset ℕ} (τ : Fin t → Bool) (hUV : V ⊆ U) (hU : D_GoodU U τ) :
    D_GoodU V τ := fun k hk => hU k (hUV hk)

/-- The letters of the blocks with `k ∉ U` do not change. -/
lemma D_xb_flip_out {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) {i : ℕ} (hi : ¬ (1 ≤ i ∧ (i + 1) / 2 ∈ U)) :
    D_xb (D_flipU U τ) i = D_xb τ i := by
  rw [D_xb_flipU]; split_ifs with h
  · exact absurd h.2 hi
  · rfl

lemma D_xb_flip_in {t : ℕ} (U : Finset ℕ) (τ : Fin t → Bool) {i : ℕ} (hit : i < t)
    (hi : 1 ≤ i ∧ (i + 1) / 2 ∈ U) : D_xb (D_flipU U τ) i = !D_xb τ i := by
  rw [D_xb_flipU]; simp [hit, hi]

/-- Composition of swaps: if `k ∉ U` then `flip (insert k U) = flip {k} ∘ flip U`. -/
lemma D_flipU_insert {t : ℕ} (U : Finset ℕ) (k : ℕ) (hk : k ∉ U) (τ : Fin t → Bool) :
    D_flipU (insert k U) τ = D_flipU {k} (D_flipU U τ) := by
  funext i
  unfold D_flipU
  simp only [mem_insert, mem_singleton]
  by_cases h1 : 1 ≤ (i : ℕ)
  · by_cases h2 : ((i : ℕ) + 1) / 2 = k
    · simp [h1, h2, hk]
    · by_cases h3 : ((i : ℕ) + 1) / 2 ∈ U <;> simp [h1, h2, h3]
  · simp [h1]

/-! ## Closed form of `c_x` -/

/-- Closed form of `c` along an orbit: `c_j(m) = Σ_{i<j, odd} 3^{o_j − o_{i+1}} 2^i`. -/
lemma D_c_closed (m j : ℕ) :
    c m j = ∑ i ∈ range j, (if T^[i] m % 2 = 1 then 3 ^ (o m j - o m (i + 1)) * 2 ^ i else 0) := by
  induction j with
  | zero => simp [c]
  | succ j ih =>
    have hmono : ∀ i < j, o m (i + 1) ≤ o m j := by
      intro i hi
      have : ∀ a b, a ≤ b → o m a ≤ o m b := by
        intro a b hab
        induction b with
        | zero => simp_all
        | succ b ihb =>
          rcases Nat.lt_or_ge a (b + 1) with h' | h'
          · exact (ihb (by omega)).trans (Collatz.o_le_succ m b)
          · rw [show a = b + 1 by omega]
      exact this _ _ (by omega)
    rw [sum_range_succ]
    by_cases h : T^[j] m % 2 = 1
    · have ho : o m (j + 1) = o m j + 1 := by simp [o, h]
      simp only [c, h, ite_true, ho, ih, mul_sum]
      rw [Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply sum_congr rfl
      intro i hi
      have := hmono i (mem_range.mp hi)
      split_ifs
      · rw [show o m j + 1 - o m (i + 1) = (o m j - o m (i + 1)) + 1 by omega, pow_succ]; ring
      · simp
    · have ho : o m (j + 1) = o m j := by simp [o, h]
      simp only [c, h, ite_false, ho, ih, add_zero]

/-- Closed form of `c` on words. -/
def D_cw {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i ∈ range n, (if D_xb x i then 3 ^ (ones x n - ones x (i + 1)) * 2 ^ i else 0)

lemma D_parity_mOf {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (T^[i] (mOf x) % 2 = 1) ↔ D_xb x i = true := by
  have h := congrFun (pw_mOf x) ⟨i, hi⟩
  simp only [pw] at h
  rw [D_xb_lt x hi, ← h]
  simp

lemma D_o_mOf {n : ℕ} (x : Fin n → Bool) {j : ℕ} (hj : j ≤ n) : o (mOf x) j = ones x j := by
  induction j with
  | zero => simp [o, D_ones_zero]
  | succ j ih =>
    rw [D_ones_succ, ← ih (by omega)]
    simp only [o]
    congr 1
    have := D_parity_mOf x (i := j) (by omega)
    by_cases h : T^[j] (mOf x) % 2 = 1
    · simp [h, this.mp h]
    · have h' : D_xb x j = false := by
        cases hx : D_xb x j
        · rfl
        · exact absurd (this.mpr hx) h
      simp [h, h']

lemma D_cOf_eq {n : ℕ} (x : Fin n → Bool) : cOf x = D_cw x := by
  unfold cOf D_cw
  rw [D_c_closed]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [D_o_mOf x le_rfl, D_o_mOf x (by omega)]
  have := D_parity_mOf x hi'
  by_cases h : T^[i] (mOf x) % 2 = 1
  · simp [h, this.mp h]
  · have h' : D_xb x i = false := by
      cases hx : D_xb x i
      · rfl
      · exact absurd (this.mpr hx) h
    simp [h, h']

/-! ## Change of `c` under the swap (the combinatorial part of Lemma 5.3 (ii)) -/

/-- The individual terms of `D_cw`. -/
def D_cterm {n : ℕ} (x : Fin n → Bool) (i : ℕ) : ℕ :=
  if D_xb x i then 3 ^ (ones x n - ones x (i + 1)) * 2 ^ i else 0

lemma D_cw_eq_sum {n : ℕ} (x : Fin n → Bool) : D_cw x = ∑ i ∈ range n, D_cterm x i := rfl

/-- The sign `ε_k`: `+1` if the block is `10`, `−1` if it is `01`. -/
def D_eps {t : ℕ} (τ : Fin t → Bool) (k : ℕ) : ℤ := if D_xb τ (2 * k - 1) then 1 else -1

/-- Change of `c` under the swap of a single block: `c(τ') = c(τ) + ε 3^{L'−j} 2^{2k−1}`. -/
lemma D_cw_flip1 {t : ℕ} (τ : Fin t → Bool) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 * k < t)
    (hne : D_xb τ (2 * k - 1) ≠ D_xb τ (2 * k)) :
    (D_cw (D_flipU {k} τ) : ℤ) = D_cw τ +
      D_eps τ k * 3 ^ (ones τ t - (ones τ (2 * k - 1) + 1)) * 2 ^ (2 * k - 1) := by
  have hG : D_GoodU {k} τ := by
    intro k' hk'; rw [mem_singleton] at hk'; subst hk'; exact ⟨hk1, hk2, hne⟩
  have htot := D_ones_flip_total {k} τ hG
  have hout : ∀ i, i ≠ 2 * k - 1 → i ≠ 2 * k → D_cterm (D_flipU {k} τ) i = D_cterm τ i := by
    intro i h1 h2
    unfold D_cterm
    rw [D_xb_flip_out {k} τ (by simp only [mem_singleton]; omega),
      D_ones_flip_eq {k} τ hG (i + 1) (by simp only [mem_singleton]; omega), htot]
  have hsum : (∑ i ∈ range t, (D_cterm (D_flipU {k} τ) i : ℤ)) - ∑ i ∈ range t, (D_cterm τ i : ℤ) =
      ∑ i ∈ ({2 * k - 1, 2 * k} : Finset ℕ), ((D_cterm (D_flipU {k} τ) i : ℤ) - D_cterm τ i) := by
    rw [← sum_sub_distrib]; symm
    apply sum_subset
    · intro i hi; simp only [mem_insert, mem_singleton] at hi; rw [mem_range]; omega
    · intro i _ hi
      simp only [mem_insert, mem_singleton, not_or] at hi
      rw [hout i hi.1 hi.2]; ring
  rw [sum_pair (by omega)] at hsum
  rw [D_cw_eq_sum, D_cw_eq_sum]
  push_cast
  rw [← sub_eq_iff_eq_add', hsum]
  -- Computing the value
  have hin1 : D_xb (D_flipU {k} τ) (2 * k - 1) = !D_xb τ (2 * k - 1) :=
    D_xb_flip_in {k} τ (by omega) (by simp only [mem_singleton]; omega)
  have hin2 : D_xb (D_flipU {k} τ) (2 * k) = !D_xb τ (2 * k) :=
    D_xb_flip_in {k} τ (by omega) (by simp only [mem_singleton]; omega)
  have hb1 : ones τ (2 * k) = ones τ (2 * k - 1) + (if D_xb τ (2 * k - 1) then 1 else 0) := by
    have := D_ones_succ τ (2 * k - 1); rwa [show 2 * k - 1 + 1 = 2 * k by omega] at this
  have hb2 : ones τ (2 * k + 1) = ones τ (2 * k) + (if D_xb τ (2 * k) then 1 else 0) := D_ones_succ _ _
  have hb3 : ones (D_flipU {k} τ) (2 * k) =
      ones τ (2 * k - 1) + (if !D_xb τ (2 * k - 1) then 1 else 0) := by
    have := D_ones_succ (D_flipU {k} τ) (2 * k - 1)
    rwa [show 2 * k - 1 + 1 = 2 * k by omega, D_ones_flip_blockstart {k} τ hG k, hin1] at this
  have hb4 : ones (D_flipU {k} τ) (2 * k + 1) = ones τ (2 * k + 1) :=
    D_ones_flip_odd' {k} τ hG (by omega)
  unfold D_cterm D_eps
  rw [hin1, hin2, show 2 * k - 1 + 1 = 2 * k by omega, hb3, hb4, htot, hb2, hb1]
  have hp : (2:ℤ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    rw [← pow_succ']; congr 1; omega
  revert hne
  cases D_xb τ (2 * k - 1) <;> cases D_xb τ (2 * k) <;> intro hne <;> simp at hne ⊢ <;>
    push_cast <;> rw [hp] <;> ring

lemma D_flipU_empty {t : ℕ} (τ : Fin t → Bool) : D_flipU ∅ τ = τ := by
  funext i; simp [D_flipU]

/-- Change of `c` under the swap (general `U`). -/
lemma D_cw_flipU {t : ℕ} (τ : Fin t → Bool) (U : Finset ℕ) (hU : D_GoodU U τ) :
    (D_cw (D_flipU U τ) : ℤ) = D_cw τ +
      ∑ k ∈ U, D_eps τ k * 3 ^ (ones τ t - (ones τ (2 * k - 1) + 1)) * 2 ^ (2 * k - 1) := by
  induction U using Finset.induction_on with
  | empty => simp [D_flipU_empty]
  | insert k U hk ih =>
    have hU' : D_GoodU U τ := D_GoodU_mono τ (subset_insert k U) hU
    obtain ⟨hk1, hk2, hk3⟩ := hU k (mem_insert_self k U)
    have hx1 : D_xb (D_flipU U τ) (2 * k - 1) = D_xb τ (2 * k - 1) :=
      D_xb_flip_out U τ (by rw [show 2 * k - 1 + 1 = 2 * k by omega, Nat.mul_div_cancel_left k two_pos]; tauto)
    have hx2 : D_xb (D_flipU U τ) (2 * k) = D_xb τ (2 * k) :=
      D_xb_flip_out U τ (by rw [show (2 * k + 1) / 2 = k by omega]; tauto)
    rw [D_flipU_insert U k hk, D_cw_flip1 (D_flipU U τ) k hk1 hk2 (by rw [hx1, hx2]; exact hk3), ih hU',
      sum_insert hk, D_ones_flip_total U τ hU', D_ones_flip_blockstart U τ hU' k]
    unfold D_eps; rw [hx1]; ring

end Collatz.M1
