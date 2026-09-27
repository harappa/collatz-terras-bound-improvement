import CollatzProof.M1.Defs

/-!
# Auxiliary results for §6: the mode of the binomial distribution

Step 4 of Lemma 6.2: the mean `k` of `Bin(N, k/N)` is an integer, hence a mode, and its probability is at least `1/(N+1)` (`E_mode`).
-/

namespace Collatz.M1

open Finset

/-! ## The mode of the binomial distribution (step 4 of Lemma 6.2) -/

/-- `F(j) = C(N, j) k^j (N − k)^{N−j}` (`N^N` times the probability of `Bin(N, k/N)`). -/
def E_F (N k j : ℕ) : ℕ := N.choose j * k ^ j * (N - k) ^ (N - j)

theorem E_F_step (N k j : ℕ) (hj : j < N) :
    E_F N k (j + 1) * ((j + 1) * (N - k)) = E_F N k j * ((N - j) * k) := by
  unfold E_F
  have h1 := Nat.choose_succ_right_eq N j
  obtain ⟨r, hr1, hr2⟩ : ∃ r, N - (j + 1) = r ∧ N - j = r + 1 := ⟨N - (j + 1), rfl, by omega⟩
  rw [hr2] at h1
  rw [hr1, hr2]
  calc N.choose (j + 1) * k ^ (j + 1) * (N - k) ^ r * ((j + 1) * (N - k))
      = (N.choose (j + 1) * (j + 1)) * (k ^ (j + 1) * (N - k) ^ (r + 1)) := by ring
    _ = (N.choose j * (r + 1)) * (k ^ (j + 1) * (N - k) ^ (r + 1)) := by rw [h1]
    _ = N.choose j * k ^ j * (N - k) ^ (r + 1) * ((r + 1) * k) := by ring

theorem E_F_up (N k j : ℕ) (hjk : j + 1 ≤ k) (hkN : k ≤ N) : E_F N k j ≤ E_F N k (j + 1) := by
  by_cases hk : k = N
  · subst hk
    have : E_F k k j = 0 := by
      unfold E_F
      rw [Nat.sub_self, zero_pow (by omega), mul_zero]
    rw [this]; exact Nat.zero_le _
  · have hpos : 0 < (j + 1) * (N - k) := Nat.mul_pos (by omega) (by omega)
    have step := E_F_step N k j (by omega)
    have ineq : (j + 1) * (N - k) ≤ (N - j) * k := by
      obtain ⟨a, rfl⟩ : ∃ a, N = k + a := ⟨N - k, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, k = j + 1 + b := ⟨k - (j + 1), by omega⟩
      rw [show j + 1 + b + a - (j + 1 + b) = a by omega, show j + 1 + b + a - j = 1 + b + a by omega]
      nlinarith
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc E_F N k j * ((j + 1) * (N - k)) ≤ E_F N k j * ((N - j) * k) := Nat.mul_le_mul_left _ ineq
      _ = E_F N k (j + 1) * ((j + 1) * (N - k)) := step.symm

theorem E_F_down (N k j : ℕ) (hkj : k ≤ j) (hjN : j < N) : E_F N k (j + 1) ≤ E_F N k j := by
  have hpos : 0 < (j + 1) * (N - k) := Nat.mul_pos (by omega) (by omega)
  have step := E_F_step N k j hjN
  have ineq : (N - j) * k ≤ (j + 1) * (N - k) := by
    obtain ⟨a, rfl⟩ : ∃ a, j = k + a := ⟨j - k, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, N = k + a + 1 + b := ⟨N - (k + a + 1), by omega⟩
    rw [show k + a + 1 + b - (k + a) = 1 + b by omega, show k + a + 1 + b - k = a + 1 + b by omega]
    nlinarith
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc E_F N k (j + 1) * ((j + 1) * (N - k)) = E_F N k j * ((N - j) * k) := step
    _ ≤ E_F N k j * ((j + 1) * (N - k)) := Nat.mul_le_mul_left _ ineq

theorem E_F_le_mode (N k j : ℕ) (hk : k ≤ N) (hj : j ≤ N) : E_F N k j ≤ E_F N k k := by
  rcases le_total j k with h | h
  · have key : ∀ i, i ≤ k → E_F N k (k - i) ≤ E_F N k k := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        calc E_F N k (k - (i + 1)) ≤ E_F N k (k - (i + 1) + 1) := E_F_up N k _ (by omega) hk
          _ = E_F N k (k - i) := by rw [show k - (i + 1) + 1 = k - i by omega]
          _ ≤ E_F N k k := ih (by omega)
    have := key (k - j) (by omega)
    rwa [show k - (k - j) = j by omega] at this
  · have key : ∀ i, k + i ≤ N → E_F N k (k + i) ≤ E_F N k k := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        calc E_F N k (k + (i + 1)) = E_F N k (k + i + 1) := by rw [Nat.add_assoc]
          _ ≤ E_F N k (k + i) := E_F_down N k _ (by omega) (by omega)
          _ ≤ E_F N k k := ih (by omega)
    have := key (j - k) (by omega)
    rwa [show k + (j - k) = j by omega] at this

theorem E_F_sum (N k : ℕ) (hk : k ≤ N) : N ^ N ≤ (N + 1) * E_F N k k := by
  have hsum : ∑ j ∈ range (N + 1), E_F N k j = N ^ N := by
    have := add_pow (k : ℕ) (N - k) N
    rw [Nat.add_sub_cancel' hk] at this
    rw [this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold E_F; simp only [Nat.cast_id]; ring
  rw [← hsum]
  calc ∑ j ∈ range (N + 1), E_F N k j ≤ ∑ _j ∈ range (N + 1), E_F N k k :=
        Finset.sum_le_sum (fun j hj => E_F_le_mode N k j hk (by simp at hj; omega))
    _ = (N + 1) * E_F N k k := by simp

/-- The probability of the binomial distribution `Bin(N, k/N)` at its mean `k` is at least `1/(N+1)`. -/
theorem E_mode (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    1 ≤ ((N : ℝ) + 1) * (N.choose k : ℝ) * ((k : ℝ) / N) ^ k * (1 - (k : ℝ) / N) ^ (N - k) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : 1 - (k : ℝ) / N = ((N - k : ℕ) : ℝ) / N := by
    rw [Nat.cast_sub hk]; field_simp
  have hsum : ((N : ℝ)) ^ N ≤ ((N : ℝ) + 1) * (N.choose k : ℝ) * (k : ℝ) ^ k *
      ((N - k : ℕ) : ℝ) ^ (N - k) := by
    have h := E_F_sum N k hk
    unfold E_F at h
    rw [show (N + 1) * (N.choose k * k ^ k * (N - k) ^ (N - k)) =
      (N + 1) * N.choose k * k ^ k * (N - k) ^ (N - k) by ring] at h
    exact_mod_cast h
  have hpow : ((N : ℝ)) ^ k * ((N : ℝ)) ^ (N - k) = (N : ℝ) ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [e1, div_pow, div_pow]
  rw [show ((N : ℝ) + 1) * (N.choose k : ℝ) * ((k : ℝ) ^ k / (N : ℝ) ^ k) *
      (((N - k : ℕ) : ℝ) ^ (N - k) / (N : ℝ) ^ (N - k)) =
      (((N : ℝ) + 1) * (N.choose k : ℝ) * (k : ℝ) ^ k * ((N - k : ℕ) : ℝ) ^ (N - k)) /
        ((N : ℝ) ^ k * (N : ℝ) ^ (N - k)) by
      field_simp]
  rw [hpow, le_div_iff₀ (pow_pos hNpos N), one_mul]
  exact hsum

end Collatz.M1
