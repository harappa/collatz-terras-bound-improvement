import CollatzProof.M1.Counting

/-!
# Auxiliary (1) for Theorem A: words and numbers

Elementary facts relating words and numbers, used in the proof of Theorem A (§4).
- The forward direction of the Terras bijection (if `n ≡ n' (mod 2^k)`, the parities of the first `k` steps agree), and `mOf (pw n k) = n mod 2^k`.
- Lemma 1.2 (iii): `T^k(n) = T^k(n mod 2^k) + 3^{o_k(n)} ⌊n/2^k⌋`.
- Agreement of the number of 1s `ones` of a word with the number of odd steps `o`, additivity under concatenation, and the decomposition of survival (Lemma 1.5).
- The sign of the height as an integer comparison: `j ≤ λk ⟺ 2^j ≤ 3^k`.
-/

namespace Collatz.M1

open Finset

/-! ## The forward direction of the Terras bijection -/

/-- If `n ≡ n' (mod 2^{k+1})`, then `T n ≡ T n' (mod 2^k)`. -/
lemma C_T_mod (k n n' : ℕ) (h : n % 2 ^ (k + 1) = n' % 2 ^ (k + 1)) :
    T n % 2 ^ k = T n' % 2 ^ k := by
  have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [e] at h
  have hpar : n % 2 = n' % 2 := by
    have h2 : (2:ℕ) ∣ 2 * 2 ^ k := dvd_mul_right 2 _
    rw [← Nat.mod_mod_of_dvd n h2, ← Nat.mod_mod_of_dvd n' h2, h]
  have key : ∀ x x' : ℕ, x % (2 * 2 ^ k) = x' % (2 * 2 ^ k) →
      (x / 2) % 2 ^ k = (x' / 2) % 2 ^ k := by
    intro x x' hx
    rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, hx]
  unfold T
  split_ifs with h1 h2 h2
  · exact key n n' h
  · omega
  · omega
  · apply key
    exact (Nat.ModEq.mul_left 3 h).add_right 1

/-- If `n ≡ n' (mod 2^k)`, then for `i ≤ k`, `T^i n ≡ T^i n' (mod 2^{k−i})`. -/
lemma C_iter_mod (k : ℕ) : ∀ i ≤ k, ∀ n n' : ℕ, n % 2 ^ k = n' % 2 ^ k →
    T^[i] n % 2 ^ (k - i) = T^[i] n' % 2 ^ (k - i) := by
  intro i
  induction i with
  | zero => intro _ n n' h; simpa using h
  | succ i ih =>
    intro hi n n' h
    have := ih (by omega) n n' h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply C_T_mod
    have e : k - (i + 1) + 1 = k - i := by omega
    rw [e]; exact this

/-- The parities of the first `k` steps are determined by `n mod 2^k`. -/
lemma C_par_mod (k n n' : ℕ) (h : n % 2 ^ k = n' % 2 ^ k) :
    ∀ i < k, T^[i] n % 2 = T^[i] n' % 2 := by
  intro i hi
  have := C_iter_mod k i hi.le n n' h
  have h2 : (2:ℕ) ∣ 2 ^ (k - i) := dvd_pow_self 2 (by omega)
  rw [← Nat.mod_mod_of_dvd (T^[i] n) h2, ← Nat.mod_mod_of_dvd (T^[i] n') h2, this]

lemma C_pw_mod (n k : ℕ) : pw (n % 2 ^ k) k = pw n k := by
  funext i
  unfold pw
  rw [C_par_mod k (n % 2 ^ k) n (Nat.mod_mod _ _) i i.2]

lemma C_pw_eq_of_mod (n n' k : ℕ) (h : n % 2 ^ k = n' % 2 ^ k) : pw n k = pw n' k := by
  rw [← C_pw_mod n k, ← C_pw_mod n' k, h]

/-- `mOf (pw n k) = n mod 2^k`. -/
lemma C_mOf_pw (n k : ℕ) : mOf (pw n k) = n % 2 ^ k := by
  have hlt : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have : (terrasEquiv k).symm (pw n k) = ⟨n % 2 ^ k, hlt⟩ := by
    rw [Equiv.symm_apply_eq]
    simp [terrasEquiv, C_pw_mod]
  unfold mOf; rw [this]

/-- A number in `[0, 2^k)` is determined by its word. -/
lemma C_eq_of_pw (k n n' : ℕ) (hn : n < 2 ^ k) (hn' : n' < 2 ^ k) (h : pw n k = pw n' k) :
    n = n' := by
  have h1 := C_mOf_pw n k
  have h2 := C_mOf_pw n' k
  rw [h] at h1
  rw [Nat.mod_eq_of_lt hn] at h1
  rw [Nat.mod_eq_of_lt hn'] at h2
  omega

/-! ## Lemma 1.2 (iii) -/

/-- Lemma 1.2 (iii): `T^k(n) = T^k(n mod 2^k) + 3^{o_k(n)} ⌊n/2^k⌋`. -/
lemma C_iter_split (n k : ℕ) : T^[k] n = T^[k] (n % 2 ^ k) + 3 ^ (o n k) * (n / 2 ^ k) := by
  have hpar := C_par_mod k n (n % 2 ^ k) (Nat.mod_mod _ _).symm
  obtain ⟨ho, hc⟩ := o_c_eq_of_parity n (n % 2 ^ k) k hpar k le_rfl
  have d1 := dual n k
  have d2 := dual (n % 2 ^ k) k
  rw [← ho, ← hc] at d2
  have hn := Nat.mod_add_div n (2 ^ k)
  have hpos : 0 < 2 ^ k := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  have : 3 ^ o n k * n = 3 ^ o n k * (n % 2 ^ k) + 2 ^ k * (3 ^ o n k * (n / 2 ^ k)) := by
    calc 3 ^ o n k * n = 3 ^ o n k * (n % 2 ^ k + 2 ^ k * (n / 2 ^ k)) := by rw [hn]
      _ = _ := by ring
  rw [mul_add, d1, d2, this]
  ring

/-! ## `ones` and `o` -/

lemma C_ones_succ {k : ℕ} (x : Fin k → Bool) (j : ℕ) (hj : j < k) :
    ones x (j + 1) = ones x j + if x ⟨j, hj⟩ = true then 1 else 0 := by
  unfold ones
  rw [Finset.card_filter, Finset.card_filter]
  have hpt : ∀ i : Fin k, (if (i:ℕ) < j + 1 ∧ x i = true then 1 else 0) =
      (if (i:ℕ) < j ∧ x i = true then 1 else 0) +
        (if i = ⟨j, hj⟩ then (if x ⟨j, hj⟩ = true then 1 else 0) else 0) := by
    intro i
    by_cases h1 : (i:ℕ) < j
    · have hne : i ≠ ⟨j, hj⟩ := by
        intro h; rw [h] at h1; simp at h1
      have h1' : (i:ℕ) < j + 1 := by omega
      simp [h1, h1', hne]
    · by_cases h2 : (i : ℕ) = j
      · have he : i = ⟨j, hj⟩ := Fin.ext h2
        subst he
        simp
      · have hne : i ≠ ⟨j, hj⟩ := fun h => h2 (by rw [h])
        have h3 : ¬ ((i:ℕ) < j + 1) := by omega
        simp [h1, h3, hne]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma C_ones_zero {k : ℕ} (x : Fin k → Bool) : ones x 0 = 0 := by
  unfold ones; simp

lemma C_ones_le {k : ℕ} (x : Fin k → Bool) (j : ℕ) : ones x j ≤ j := by
  induction j with
  | zero => simp [C_ones_zero]
  | succ j ih =>
    by_cases hj : j < k
    · rw [C_ones_succ x j hj]; split_ifs <;> omega
    · have : ones x (j + 1) = ones x j := by
        unfold ones
        congr 1
        apply Finset.filter_congr
        intro i _
        have : (i:ℕ) < k := i.2
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      omega

/-- If `j ≥ k`, then `ones x j = ones x k`. -/
lemma C_ones_of_ge {k : ℕ} (x : Fin k → Bool) (j : ℕ) (hj : k ≤ j) : ones x j = ones x k := by
  unfold ones
  congr 1
  apply Finset.filter_congr
  intro i _
  have : (i:ℕ) < k := i.2
  constructor
  · rintro ⟨_, h2⟩; exact ⟨this, h2⟩
  · rintro ⟨_, h2⟩; exact ⟨by omega, h2⟩

/-- `ones (pw n k) j = o_j(n)` (`j ≤ k`). -/
lemma C_ones_pw (n k : ℕ) : ∀ j ≤ k, ones (pw n k) j = o n j := by
  intro j
  induction j with
  | zero => intro _; simp [C_ones_zero, o]
  | succ j ih =>
    intro hj
    rw [C_ones_succ _ j (by omega), ih (by omega)]
    simp only [o, pw]
    by_cases h : T^[j] n % 2 = 1 <;> simp [h]

/-- Additivity of `o`: `o_{a+j}(n) = o_a(n) + o_j(T^a n)`. -/
lemma C_o_add (n a : ℕ) : ∀ j, o n (a + j) = o n a + o (T^[a] n) j := by
  intro j
  induction j with
  | zero => simp [o]
  | succ j ih =>
    rw [← add_assoc]
    simp only [o]
    rw [ih, ← Function.iterate_add_apply, add_comm j a]
    ring

/-- Height: `hw y (pw n k) j = y + λ o_j(n) − j` (`j ≤ k`). -/
lemma C_hw_pw (y : ℝ) (n k j : ℕ) (hj : j ≤ k) :
    hw y (pw n k) j = y + lam * (o n j : ℝ) - j := by
  unfold hw; rw [C_ones_pw n k j hj]

/-! ## Heights and integer comparisons -/

lemma C_lam_pos : 0 < lam := by
  unfold lam; exact Real.logb_pos (by norm_num) (by norm_num)

lemma C_lam_mul (k : ℕ) : lam * (k : ℝ) = Real.logb 2 ((3:ℝ) ^ k) := by
  unfold lam; rw [Real.logb_pow]; ring

/-- `j ≤ λk ⟺ 2^j ≤ 3^k`. -/
lemma C_le_lam_iff (j k : ℕ) : (j : ℝ) ≤ lam * k ↔ 2 ^ j ≤ 3 ^ k := by
  rw [C_lam_mul, Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- `j < λk ⟺ 2^j < 3^k`. -/
lemma C_lt_lam_iff (j k : ℕ) : (j : ℝ) < lam * k ↔ 2 ^ j < 3 ^ k := by
  rw [C_lam_mul, Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- `λ L_p ≤ q < λ (L_p + 1)`. -/
lemma C_Lp_real (q : ℕ) : lam * (Lp q : ℝ) ≤ q ∧ (q : ℝ) < lam * ((Lp q : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := Lp_spec q
  constructor
  · rw [C_lam_mul, Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
    exact_mod_cast h1
  · have := (C_lt_lam_iff q (Lp q + 1)).2 h2
    push_cast at this; exact this

/-! ## Decomposition of survival (Lemma 1.5) -/

/-- Lemma 1.5: survival of a word of length `s + q` splits into survival of the first part and survival of the second part from height `h_L`. -/
lemma C_surv_split (n s q : ℕ) (h : SurvW 0 (pw n (s + q))) :
    SurvW 0 (pw n s) ∧ SurvW (hL s (o n s)) (pw (T^[s] n) q) := by
  constructor
  · intro j hj1 hj2
    have := h j hj1 (by omega)
    rw [C_hw_pw _ _ _ _ (by omega)] at this
    rw [C_hw_pw _ _ _ _ hj2]; exact this
  · intro j hj1 hj2
    have := h (s + j) (by omega) (by omega)
    rw [C_hw_pw _ _ _ _ (by omega), C_o_add] at this
    rw [C_hw_pw _ _ _ _ hj2]
    unfold hL
    push_cast at this ⊢
    linarith

lemma C_mem_Eset (m q : ℕ) (y : ℝ) (h : SurvW y (pw m q)) : m % 2 ^ q ∈ Eset q y := by
  simp only [Eset, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.mod_lt _ (by positivity), by rw [C_pw_mod]; exact h⟩

end Collatz.M1
