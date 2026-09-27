import CollatzProof.M1.C_Words

/-!
# Auxiliary (4) for Theorem A: counting words with a fixed number of 1s (Chernoff form)

From `#{x ∈ {0,1}^n | |x| = k} · a^k b^{n−k} ≤ (a + b)^n` (one term of the binomial theorem):
- `a = ρ_c`, `b = 1 − ρ_c`: `#{|x| = k} ≤ 2^{(1−c)n − t*(λk − n)}` (the same computation as Lemmas 2.2 and 2.3, Lemma 1.7),
- `a = ρ_c z`, `b = 1 − ρ_c`: the tilted form `#{|x| = k} ≤ 2^{(1−c)n − t*(λk − n)} (1 + ρ_c(z − 1))^n / z^k`.
-/

namespace Collatz.M1

open Finset

/-- The set of words of length `n` with `k` 1s. -/
noncomputable def C_W (n k : ℕ) : Finset (Fin n → Bool) := by
  classical
  exact univ.filter (fun x : Fin n → Bool => ones x n = k)

lemma C_mem_W {n k : ℕ} (x : Fin n → Bool) : x ∈ C_W n k ↔ ones x n = k := by
  classical
  simp [C_W]

/-- `ones x n` is the number of `i` with `x i = true`. -/
lemma C_ones_full {n : ℕ} (x : Fin n → Bool) :
    ones x n = (univ.filter (fun i : Fin n => x i = true)).card := by
  classical
  unfold ones
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [i.2]

/-- `Π_i (if x_i then a else b) = a^{|x|} b^{n−|x|}`. -/
lemma C_prod_ite {n : ℕ} (x : Fin n → Bool) (a b : ℝ) :
    ∏ i, (if x i = true then a else b) = a ^ ones x n * b ^ (n - ones x n) := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, C_ones_full]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => x i = true)
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- One term of the binomial theorem: `#{|x| = k} · a^k b^{n−k} ≤ (a + b)^n`. -/
lemma C_W_le (n k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((C_W n k).card : ℝ) * (a ^ k * b ^ (n - k)) ≤ (a + b) ^ n := by
  classical
  have htot : ∑ x : Fin n → Bool, ∏ i, (if x i = true then a else b) = (a + b) ^ n := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Bool) => if j = true then a else b)]
    simp [Finset.prod_const]
  rw [← htot, ← Finset.sum_filter_add_sum_filter_not univ (fun x : Fin n → Bool => ones x n = k)]
  have h1 : ∑ x ∈ univ.filter (fun x : Fin n → Bool => ones x n = k),
      ∏ i, (if x i = true then a else b) = ((C_W n k).card : ℝ) * (a ^ k * b ^ (n - k)) := by
    rw [Finset.sum_congr rfl (g := fun _ => a ^ k * b ^ (n - k))]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 2
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [C_prod_ite, hx.2]
  rw [h1]
  have h2 : 0 ≤ ∑ x ∈ univ.filter (fun x : Fin n → Bool => ¬ ones x n = k),
      ∏ i, (if x i = true then a else b) := by
    apply Finset.sum_nonneg; intro x _
    apply Finset.prod_nonneg; intro i _
    split_ifs <;> assumption
  linarith

/-! ## `ρ_c` in terms of powers of `2` -/

lemma C_two_f : 2 * ff = (2:ℝ) ^ (1 - cc) := by
  unfold ff
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]
  field_simp

lemma C_rhoc_eq : rhoc = (2:ℝ) ^ (tstar * aa - (1 - cc)) := by
  rw [lemma17.2.1, C_two_f, ← Real.rpow_sub (by norm_num)]

lemma C_rhoc_compl_eq : 1 - rhoc = (2:ℝ) ^ (-tstar - (1 - cc)) := by
  rw [lemma17.2.2, C_two_f, ← Real.rpow_sub (by norm_num)]

lemma C_aa_eq : aa = lam - 1 := rfl

/-- `ρ_c^k (1 − ρ_c)^{n−k} = 2^{t*(λk − n) − (1−c)n}` (`k ≤ n`). -/
lemma C_rho_pow (n k : ℕ) (hk : k ≤ n) :
    rhoc ^ k * (1 - rhoc) ^ (n - k) = (2:ℝ) ^ (tstar * (lam * k - n) - (1 - cc) * n) := by
  rw [C_rhoc_compl_eq, C_rhoc_eq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  rw [Nat.cast_sub hk, C_aa_eq]
  ring

lemma C_rhoc_pos : 0 < rhoc := by rw [C_rhoc_eq]; positivity
lemma C_rhoc_lt_one : rhoc < 1 := by
  have : 0 < 1 - rhoc := by rw [C_rhoc_compl_eq]; positivity
  linarith

/-- Chernoff form: `#{|x| = k} ≤ 2^{(1−c)n − t*(λk − n)}`. -/
lemma C_W_bound (n k : ℕ) :
    ((C_W n k).card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * n - tstar * (lam * k - n)) := by
  by_cases hk : k ≤ n
  · have h := C_W_le n k rhoc (1 - rhoc) C_rhoc_pos.le (by linarith [C_rhoc_lt_one])
    rw [C_rho_pow n k hk, add_sub_cancel, one_pow] at h
    have hpos : (0:ℝ) < (2:ℝ) ^ (tstar * (lam * k - n) - (1 - cc) * n) := by positivity
    have : ((C_W n k).card : ℝ) ≤ 1 / (2:ℝ) ^ (tstar * (lam * k - n) - (1 - cc) * n) := by
      rw [le_div_iff₀ hpos]; exact h
    refine this.trans_eq ?_
    rw [one_div, ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  · have : C_W n k = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      rw [C_mem_W] at hx
      have := C_ones_le x n
      omega
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Tilted Chernoff form: for `z > 0`, `#{|x| = k} ≤ 2^{(1−c)n − t*(λk − n)} (1 + ρ_c(z−1))^n / z^k`. -/
lemma C_W_bound_tilt (n k : ℕ) (z : ℝ) (hz : 0 < z) :
    ((C_W n k).card : ℝ) ≤
      (2:ℝ) ^ ((1 - cc) * n - tstar * (lam * k - n)) * ((1 + rhoc * (z - 1)) ^ n / z ^ k) := by
  by_cases hk : k ≤ n
  · have h := C_W_le n k (rhoc * z) (1 - rhoc) (by have := C_rhoc_pos; positivity)
      (by linarith [C_rhoc_lt_one])
    have e1 : (rhoc * z) ^ k * (1 - rhoc) ^ (n - k) = z ^ k * (rhoc ^ k * (1 - rhoc) ^ (n - k)) := by
      rw [mul_pow]; ring
    rw [e1, C_rho_pow n k hk] at h
    have e2 : rhoc * z + (1 - rhoc) = 1 + rhoc * (z - 1) := by ring
    rw [e2] at h
    have hpos : (0:ℝ) < z ^ k * (2:ℝ) ^ (tstar * (lam * k - n) - (1 - cc) * n) := by positivity
    have : ((C_W n k).card : ℝ) ≤ (1 + rhoc * (z - 1)) ^ n /
        (z ^ k * (2:ℝ) ^ (tstar * (lam * k - n) - (1 - cc) * n)) := by
      rw [le_div_iff₀ hpos]; exact h
    refine this.trans_eq ?_
    have e3 : (2:ℝ) ^ ((1 - cc) * n - tstar * (lam * k - n)) =
        1 / (2:ℝ) ^ (tstar * (lam * k - n) - (1 - cc) * n) := by
      rw [one_div, ← Real.rpow_neg (by norm_num)]; congr 1; ring
    rw [e3]
    field_simp
  · have : C_W n k = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      rw [C_mem_W] at hx
      have := C_ones_le x n
      omega
    rw [this, Finset.card_empty, Nat.cast_zero]
    have h1 : 0 ≤ 1 + rhoc * (z - 1) := by
      have := C_rhoc_pos; have := C_rhoc_lt_one; nlinarith
    positivity

end Collatz.M1
