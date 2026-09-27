import CollatzProof.M1.I_Kernel
import CollatzProof.M1.Counting

/-!
# Auxiliary results for §12: word weights, class sums, the recursion for the Bhattacharyya coefficients and the moment bound

- `I_Tz`: the shortcut map on the integers. `I_gw α β n x = α^{#odd steps} β^{#even steps}` (over the first `n` steps, `x ∈ ℤ`).
  For `α = √ρ_c`, `β = √(1−ρ_c)`, `I_gw α β q z = √Q_q(z)` (the `Q_n` of §12.1).
- The core of Lemma 12.1 (iii): the class sum `Σ_{z<2^n, z≡y (2^j)} g_n(z) = g_j(y)(α+β)^{n−j}` (`I_class_sum`).
- Lemma 12.3 and Proposition 12.4: the recursion for `Φ_n(c, v) = Σ_x g_n(x) g_n(cx + v)` (`c` odd; the `3^b` of the manuscript is generalized to an arbitrary odd number) and
  `Σ_v Φ_n(c, v)^p ≤ (1 + (2αβ)^p)^n` (`I_moment`).
-/

namespace Collatz.M1

open Finset

/-- The shortcut map on the integers. -/
def I_Tz (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- The word weight `g_n(x)` (multiply by `α` (odd) or `β` (even) according to the parities of the first `n` steps). -/
noncomputable def I_gw (α β : ℝ) : ℕ → ℤ → ℝ
  | 0, _ => 1
  | n + 1, x => (if x % 2 = 0 then β else α) * I_gw α β n (I_Tz x)

section gw

variable {α β : ℝ}

lemma I_gw_zero (x : ℤ) : I_gw α β 0 x = 1 := rfl

lemma I_gw_succ (n : ℕ) (x : ℤ) :
    I_gw α β (n + 1) x = (if x % 2 = 0 then β else α) * I_gw α β n (I_Tz x) := rfl

lemma I_gw_even (n : ℕ) (y : ℤ) (h : y % 2 = 0) : I_gw α β (n + 1) y = β * I_gw α β n (y / 2) := by
  rw [I_gw_succ, if_pos h]; unfold I_Tz; rw [if_pos h]

lemma I_gw_odd (n : ℕ) (y : ℤ) (h : y % 2 = 1) :
    I_gw α β (n + 1) y = α * I_gw α β n ((3 * y + 1) / 2) := by
  have h' : ¬ y % 2 = 0 := by omega
  rw [I_gw_succ, if_neg h']; unfold I_Tz; rw [if_neg h']

lemma I_gw_per (n : ℕ) : ∀ (x k : ℤ), I_gw α β n (x + 2 ^ n * k) = I_gw α β n x := by
  induction n with
  | zero => intro x k; rfl
  | succ n ih =>
    intro x k
    have e : (2 : ℤ) ^ (n + 1) * k = 2 * (2 ^ n * k) := by ring
    rw [e]
    generalize hm : (2 : ℤ) ^ n * k = m
    rcases Int.emod_two_eq_zero_or_one x with h | h
    · rw [I_gw_even n _ (by omega), I_gw_even n _ h]
      have : (x + 2 * m) / 2 = x / 2 + 2 ^ n * k := by omega
      rw [this, ih]
    · rw [I_gw_odd n _ (by omega), I_gw_odd n _ h]
      have : (3 * (x + 2 * m) + 1) / 2 = (3 * x + 1) / 2 + 2 ^ n * (3 * k) := by
        have : (2 : ℤ) ^ n * (3 * k) = 3 * m := by rw [← hm]; ring
        omega
      rw [this, ih]

lemma I_gw_congr (n : ℕ) (x y : ℤ) (h : (2 : ℤ) ^ n ∣ x - y) : I_gw α β n x = I_gw α β n y := by
  obtain ⟨k, hk⟩ := h
  have : x = y + 2 ^ n * k := by linarith
  rw [this, I_gw_per]

lemma I_gw_nonneg (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) : ∀ x : ℤ, 0 ≤ I_gw α β n x := by
  induction n with
  | zero => intro x; simp [I_gw_zero]
  | succ n ih =>
    intro x; rw [I_gw_succ]
    apply mul_nonneg _ (ih _)
    split_ifs <;> assumption

lemma I_gw_mul (α' β' : ℝ) (n : ℕ) : ∀ x : ℤ,
    I_gw α β n x * I_gw α' β' n x = I_gw (α * α') (β * β') n x := by
  induction n with
  | zero => intro x; simp [I_gw_zero]
  | succ n ih =>
    intro x; simp only [I_gw_succ]
    rw [← ih]
    split_ifs <;> ring

/-- On the natural numbers, `g_n(z) = Π_{i<n} (α if T^i(z) is odd, β if it is even)`. -/
lemma I_gw_nat (n : ℕ) : ∀ z : ℕ,
    I_gw α β n (z : ℤ) = ∏ i : Fin n, (if T^[(i : ℕ)] z % 2 = 1 then α else β) := by
  induction n with
  | zero => intro z; simp [I_gw_zero]
  | succ n ih =>
    intro z
    rw [I_gw_succ, Fin.prod_univ_succ]
    have hT : I_Tz (z : ℤ) = ((T z : ℕ) : ℤ) := by
      unfold I_Tz T; split_ifs <;> omega
    rw [hT, ih]
    congr 1
    · simp only [Fin.val_zero, Function.iterate_zero, id_eq]
      rcases Nat.mod_two_eq_zero_or_one z with h | h
      · have h' : (z : ℤ) % 2 = 0 := by omega
        simp [h, h']
      · have h' : ¬ (z : ℤ) % 2 = 0 := by omega
        simp [h, h']

end gw

/-! ## Periodic functions and sums -/

/-- `IsCoprime 3 2^n`. -/
lemma I_coprime_three (n : ℕ) : IsCoprime (3 : ℤ) ((2 ^ n : ℕ) : ℤ) := by
  push_cast
  exact IsCoprime.pow_right ⟨1, -1, by norm_num⟩

lemma I_coprime_three' (n : ℕ) : IsCoprime ((2 : ℤ) ^ n) 3 := by
  exact IsCoprime.pow_left ⟨-1, 1, by norm_num⟩

/-- `2^j ∣ 3a ↔ 2^j ∣ a`. -/
lemma I_dvd_three_mul (j : ℕ) (a : ℤ) : (2 : ℤ) ^ j ∣ 3 * a ↔ (2 : ℤ) ^ j ∣ a :=
  ⟨fun h => (I_coprime_three' j).dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h 3⟩

/-- Class sum (the core of Lemma 12.1 (iii)): if `j ≤ n` then
`Σ_{z<2^n, 2^j ∣ z − y} g_n(z) = g_j(y)(α+β)^{n−j}`. -/
lemma I_class_sum (α β : ℝ) (n : ℕ) : ∀ (j : ℕ), j ≤ n → ∀ y : ℤ,
    ∑ z ∈ range (2 ^ n), (if (2 : ℤ) ^ j ∣ (z : ℤ) - y then I_gw α β n z else 0) =
      I_gw α β j y * (α + β) ^ (n - j) := by
  induction n with
  | zero =>
    intro j hj y
    obtain rfl : j = 0 := by omega
    simp [I_gw_zero]
  | succ n ih =>
    intro j hj y
    have hNpos : 0 < 2 ^ n := by positivity
    have hper : ∀ x : ℤ, I_gw α β n (x + ((2 ^ n : ℕ) : ℤ)) = I_gw α β n x := by
      intro x; have := I_gw_per (α := α) (β := β) n x 1; push_cast; simpa using this
    have hsum3 : ∑ x ∈ range (2 ^ n), I_gw α β n (3 * (x : ℤ) + 2) =
        ∑ x ∈ range (2 ^ n), I_gw α β n x :=
      I_sum_affine (2 ^ n) hNpos (I_gw α β n) hper 3 2 (I_coprime_three n)
    rw [pow_succ', I_sum_range_two_mul]
    push_cast
    have hE : ∀ x : ℤ, I_gw α β (n + 1) (2 * x) = β * I_gw α β n x := by
      intro x; rw [I_gw_even n _ (by omega)]; congr 2; omega
    have hO : ∀ x : ℤ, I_gw α β (n + 1) (2 * x + 1) = α * I_gw α β n (3 * x + 2) := by
      intro x; rw [I_gw_odd n _ (by omega)]; congr 2; omega
    simp_rw [hE, hO]
    rcases j with _ | j
    · simp only [pow_zero, one_dvd, ite_true, Nat.sub_zero, I_gw_zero, one_mul]
      have h0 := ih 0 (Nat.zero_le _) 0
      simp only [pow_zero, one_dvd, ite_true, Nat.sub_zero, I_gw_zero, one_mul] at h0
      rw [← mul_sum, ← mul_sum, h0, hsum3, h0]
      ring
    · have hjn : j ≤ n := by omega
      rw [show n + 1 - (j + 1) = n - j by omega]
      rcases Int.emod_two_eq_zero_or_one y with hy | hy
      · -- `y` is even: no odd `z` occurs
        have hodd : ∀ x : ℕ, ¬ (2 : ℤ) ^ (j + 1) ∣ 2 * (x : ℤ) + 1 - y := by
          intro x h
          have h2 : (2 : ℤ) ∣ 2 * (x : ℤ) + 1 - y :=
            dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero j)) h
          omega
        have heven : ∀ x : ℕ, ((2 : ℤ) ^ (j + 1) ∣ 2 * (x : ℤ) - y ↔ (2 : ℤ) ^ j ∣ (x : ℤ) - y / 2) := by
          intro x
          have : 2 * (x : ℤ) - y = ((x : ℤ) - y / 2) * 2 := by omega
          rw [this, pow_succ]
          exact mul_dvd_mul_iff_right (by norm_num)
        simp only [heven, hodd, ite_false, sum_const_zero, add_zero]
        rw [I_gw_even j y hy]
        have := ih j hjn (y / 2)
        rw [mul_assoc, ← this, mul_sum]
        apply sum_congr rfl; intro x _
        split_ifs <;> simp
      · -- `y` is odd: no even `z` occurs
        have hevn : ∀ x : ℕ, ¬ (2 : ℤ) ^ (j + 1) ∣ 2 * (x : ℤ) - y := by
          intro x h
          have h2 : (2 : ℤ) ∣ 2 * (x : ℤ) - y :=
            dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero j)) h
          omega
        have hodd : ∀ x : ℕ, ((2 : ℤ) ^ (j + 1) ∣ 2 * (x : ℤ) + 1 - y ↔
            (2 : ℤ) ^ j ∣ (3 * (x : ℤ) + 2) - (3 * (y / 2) + 2)) := by
          intro x
          have : 2 * (x : ℤ) + 1 - y = ((x : ℤ) - y / 2) * 2 := by omega
          rw [this, pow_succ, mul_dvd_mul_iff_right (by norm_num)]
          rw [show (3 * (x : ℤ) + 2) - (3 * (y / 2) + 2) = 3 * ((x : ℤ) - y / 2) by ring,
            I_dvd_three_mul]
        simp only [hevn, ite_false, sum_const_zero, zero_add, hodd]
        rw [I_gw_odd j y hy, show (3 * y + 1) / 2 = 3 * (y / 2) + 2 by omega]
        -- change of variables `t = 3x + 2`
        set G : ℤ → ℝ := fun t => if (2 : ℤ) ^ j ∣ t - (3 * (y / 2) + 2) then I_gw α β n t else 0
          with hG
        have hGper : ∀ t : ℤ, G (t + ((2 ^ n : ℕ) : ℤ)) = G t := by
          intro t
          simp only [hG]
          have hd : (2 : ℤ) ^ j ∣ ((2 ^ n : ℕ) : ℤ) := by
            push_cast; exact pow_dvd_pow 2 hjn
          have : t + ((2 ^ n : ℕ) : ℤ) - (3 * (y / 2) + 2) = (t - (3 * (y / 2) + 2)) + ((2 ^ n : ℕ) : ℤ) := by
            ring
          simp only [this, hper, dvd_add_left hd]
        have hre := I_sum_affine (2 ^ n) hNpos G hGper 3 2 (I_coprime_three n)
        have h1 : ∑ x ∈ range (2 ^ n), (if (2 : ℤ) ^ j ∣ (3 * (x : ℤ) + 2) - (3 * (y / 2) + 2) then
            α * I_gw α β n (3 * (x : ℤ) + 2) else 0) = α * ∑ x ∈ range (2 ^ n), G (3 * x + 2) := by
          rw [mul_sum]; apply sum_congr rfl; intro x _; simp only [hG]; split_ifs <;> simp
        rw [h1, hre, mul_assoc, ← ih j hjn (3 * (y / 2) + 2)]

/-- Grouping by classes: if `H` has period `2^j` then `Σ_{z<2^n} f(z)H(z) = Σ_{y<2^j} H(y) Σ_{z<2^n, 2^j ∣ z−y} f(z)`. -/
lemma I_sum_group (n j : ℕ) (f H : ℤ → ℝ) (hH : ∀ x k : ℤ, H (x + 2 ^ j * k) = H x) :
    ∑ z ∈ range (2 ^ n), f z * H z =
      ∑ y ∈ range (2 ^ j), H y * ∑ z ∈ range (2 ^ n),
        (if (2 : ℤ) ^ j ∣ (z : ℤ) - y then f z else 0) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  rw [sum_eq_single (z % 2 ^ j)]
  · rw [if_pos]
    · have : ((z : ℕ) : ℤ) = ((z % 2 ^ j : ℕ) : ℤ) + 2 ^ j * ((z / 2 ^ j : ℕ) : ℤ) := by
        have := Nat.mod_add_div z (2 ^ j)
        exact_mod_cast this.symm
      rw [mul_comm]; congr 1
      rw [this, hH]
    · have := Nat.mod_add_div z (2 ^ j)
      refine ⟨((z / 2 ^ j : ℕ) : ℤ), ?_⟩
      have h' : ((z : ℕ) : ℤ) = ((z % 2 ^ j : ℕ) : ℤ) + 2 ^ j * ((z / 2 ^ j : ℕ) : ℤ) := by
        exact_mod_cast this.symm
      rw [h']; ring
  · intro y hy hne
    rw [if_neg, mul_zero]
    intro hd
    apply hne
    rw [mem_range] at hy
    have hmod : y ≡ z [MOD 2 ^ j] := by
      rw [Nat.modEq_iff_dvd]; push_cast; exact hd
    rw [Nat.ModEq, Nat.mod_eq_of_lt hy] at hmod
    exact hmod
  · intro h; exact absurd (mem_range.mpr (Nat.mod_lt z (by positivity))) h

/-! ## The recursion for `Φ_n(c, v)` (Lemma 12.3) and the moments (Proposition 12.4) -/

/-- `Φ_n(c, v) = Σ_{x<2^n} g_n(x) g_n(cx + v)`. -/
noncomputable def I_Phi (α β : ℝ) (n : ℕ) (c v : ℤ) : ℝ :=
  ∑ x ∈ range (2 ^ n), I_gw α β n x * I_gw α β n (c * x + v)

section Phi

variable {α β : ℝ}

lemma I_Phi_nonneg (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) (c v : ℤ) : 0 ≤ I_Phi α β n c v :=
  sum_nonneg fun _ _ => mul_nonneg (I_gw_nonneg hα hβ _ _) (I_gw_nonneg hα hβ _ _)

lemma I_Phi_per (n : ℕ) (c v : ℤ) : I_Phi α β n c (v + ((2 ^ n : ℕ) : ℤ)) = I_Phi α β n c v := by
  unfold I_Phi; apply sum_congr rfl; intro x _
  congr 1
  have := I_gw_per (α := α) (β := β) n (c * x + v) 1
  push_cast; rw [← add_assoc]; simpa using this

lemma I_Phi_congr (n : ℕ) (c c' v : ℤ) (h : (2 : ℤ) ^ n ∣ c - c') :
    I_Phi α β n c v = I_Phi α β n c' v := by
  unfold I_Phi; apply sum_congr rfl; intro x _
  congr 1; apply I_gw_congr
  rw [show c * x + v - (c' * x + v) = (c - c') * x by ring]
  exact dvd_mul_of_dvd_left h _

/-- `2^{n+1} ∣ 3^{2^n} − 1`. -/
lemma I_two_pow_dvd (n : ℕ) : (2 : ℤ) ^ (n + 1) ∣ 3 ^ (2 ^ n) - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have e : (3 : ℤ) ^ (2 ^ (n + 1)) - 1 = (3 ^ (2 ^ n) - 1) * (3 ^ (2 ^ n) + 1) := by
      rw [pow_succ, pow_mul]; ring
    rw [e, pow_succ]
    apply mul_dvd_mul ih
    have : Odd ((3 : ℤ) ^ (2 ^ n)) := Odd.pow (by decide)
    obtain ⟨k, hk⟩ := this
    exact ⟨k + 1, by rw [hk]; ring⟩

/-- The form of the change of variables `t = 3x + 2`. -/
lemma I_sum_three (n : ℕ) (c w : ℤ) :
    ∑ x ∈ range (2 ^ n), I_gw α β n (3 * (x : ℤ) + 2) * I_gw α β n (c * (3 * (x : ℤ) + 2) + w) =
      I_Phi α β n c w := by
  have hper : ∀ t : ℤ, (fun t => I_gw α β n t * I_gw α β n (c * t + w)) (t + ((2 ^ n : ℕ) : ℤ)) =
      (fun t => I_gw α β n t * I_gw α β n (c * t + w)) t := by
    intro t
    simp only
    have h1 := I_gw_per (α := α) (β := β) n t 1
    have h2 := I_gw_per (α := α) (β := β) n (c * t + w) c
    push_cast
    rw [show c * (t + 2 ^ n) + w = c * t + w + 2 ^ n * c by ring, h2]
    simp at h1; rw [h1]
  exact I_sum_affine (2 ^ n) (by positivity) (fun t => I_gw α β n t * I_gw α β n (c * t + w)) hper 3 2
    (I_coprime_three n)

/-- Lemma 12.3 (`v` even): `Φ_{n+1}(c, 2v) = β²Φ_n(c, v) + α²Φ_n(c, 3v + (1−c)/2)`. -/
lemma I_Phi_even (n : ℕ) (c v : ℤ) (hc : c % 2 = 1) :
    I_Phi α β (n + 1) c (2 * v) =
      β ^ 2 * I_Phi α β n c v + α ^ 2 * I_Phi α β n c (3 * v + (1 - c) / 2) := by
  rw [← I_sum_three n c (3 * v + (1 - c) / 2)]
  unfold I_Phi
  rw [pow_succ', I_sum_range_two_mul]
  push_cast
  congr 1
  · rw [mul_sum]; apply sum_congr rfl; intro x _
    rw [I_gw_even n _ (by omega), I_gw_even n _ (by
        have : c * (2 * (x : ℤ)) + 2 * v = 2 * (c * x + v) := by ring
        rw [this]; omega)]
    have h1 : 2 * (x : ℤ) / 2 = x := by omega
    have h2 : (c * (2 * (x : ℤ)) + 2 * v) / 2 = c * x + v := by
      have : c * (2 * (x : ℤ)) + 2 * v = 2 * (c * x + v) := by ring
      rw [this]; omega
    rw [h1, h2]; ring
  · rw [mul_sum]
    apply sum_congr rfl; intro x _
    have e : c * (2 * (x : ℤ) + 1) + 2 * v = 2 * (c * x) + c + 2 * v := by ring
    rw [I_gw_odd n _ (by omega), I_gw_odd n _ (by rw [e]; omega)]
    have h1 : (3 * (2 * (x : ℤ) + 1) + 1) / 2 = 3 * x + 2 := by omega
    have h2 : (3 * (c * (2 * (x : ℤ) + 1) + 2 * v) + 1) / 2 = c * (3 * x + 2) + (3 * v + (1 - c) / 2) := by
      rw [e, show c * (3 * (x : ℤ) + 2) = 3 * (c * x) + 2 * c by ring]
      omega
    rw [h1, h2]; ring

/-- Lemma 12.3 (`v` odd): `Φ_{n+1}(c, 2v+1) = αβ(Φ_n(3c, 3v+2) + Φ_n(c', v + (c+1)/2 − 2c'))`,
`c' = c·3^{2^n − 1}` (`3c' ≡ c (mod 2^n)`). -/
lemma I_Phi_odd (n : ℕ) (c v : ℤ) (hc : c % 2 = 1) :
    I_Phi α β (n + 1) c (2 * v + 1) =
      α * β * (I_Phi α β n (3 * c) (3 * v + 2) +
        I_Phi α β n (c * 3 ^ (2 ^ n - 1)) (v + (c + 1) / 2 - 2 * (c * 3 ^ (2 ^ n - 1)))) := by
  set c' := c * 3 ^ (2 ^ n - 1) with hc'
  have h3c : 3 * c' = c * 3 ^ (2 ^ n) := by
    rw [hc', show (3 : ℤ) ^ (2 ^ n) = 3 * 3 ^ (2 ^ n - 1) by
      rw [← pow_succ']; congr 1; have := Nat.one_le_two_pow (n := n); omega]
    ring
  have hdiv : (2 : ℤ) ^ n ∣ 3 * c' - c := by
    rw [h3c, show c * 3 ^ (2 ^ n) - c = c * (3 ^ (2 ^ n) - 1) by ring]
    exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow 2 (Nat.le_succ n)) (I_two_pow_dvd n)) _
  rw [← I_sum_three n c' (v + (c + 1) / 2 - 2 * c')]
  unfold I_Phi
  rw [pow_succ', I_sum_range_two_mul]
  push_cast
  rw [mul_add]
  congr 1
  · rw [mul_sum]; apply sum_congr rfl; intro x _
    have e : c * (2 * (x : ℤ)) + (2 * v + 1) = 2 * (c * x + v) + 1 := by ring
    rw [I_gw_even n _ (by omega), I_gw_odd n _ (by rw [e]; omega)]
    have h1 : 2 * (x : ℤ) / 2 = x := by omega
    have h2 : (3 * (c * (2 * (x : ℤ)) + (2 * v + 1)) + 1) / 2 = 3 * c * x + (3 * v + 2) := by
      rw [e, show 3 * c * (x : ℤ) = 3 * (c * x) by ring]; omega
    rw [h1, h2]; ring
  · rw [mul_sum]
    apply sum_congr rfl; intro x _
    have e : c * (2 * (x : ℤ) + 1) + (2 * v + 1) = 2 * (c * x) + c + 2 * v + 1 := by ring
    rw [I_gw_odd n _ (by omega), I_gw_even n _ (by rw [e]; omega)]
    have h1 : (3 * (2 * (x : ℤ) + 1) + 1) / 2 = 3 * x + 2 := by omega
    have h2 : (c * (2 * (x : ℤ) + 1) + (2 * v + 1)) / 2 = c * x + v + (c + 1) / 2 := by
      rw [e]; omega
    rw [h1, h2]
    have h3 : I_gw α β n (c * x + v + (c + 1) / 2) =
        I_gw α β n (c' * (3 * x + 2) + (v + (c + 1) / 2 - 2 * c')) := by
      apply I_gw_congr
      rw [show c * (x : ℤ) + v + (c + 1) / 2 - (c' * (3 * x + 2) + (v + (c + 1) / 2 - 2 * c')) =
        -((3 * c' - c) * x) by ring]
      exact (dvd_neg).mpr (dvd_mul_of_dvd_left hdiv _)
    rw [h3]; ring

/-- General form of Proposition 12.4: if `α, β ≥ 0`, `α² + β² = 1`, `p ≥ 1`, and `c` is odd, then
`Σ_{v<2^n} Φ_n(c, v)^p ≤ (1 + (2αβ)^p)^n`. -/
lemma I_moment (hα : 0 ≤ α) (hβ : 0 ≤ β) (h1 : α ^ 2 + β ^ 2 = 1) (p : ℝ) (hp : 1 ≤ p) (n : ℕ) :
    ∀ c : ℤ, c % 2 = 1 → ∑ v ∈ range (2 ^ n), I_Phi α β n c v ^ p ≤ (1 + (2 * α * β) ^ p) ^ n := by
  have hp0 : 0 ≤ p := by linarith
  have hconv := convexOn_rpow hp
  have hr : 0 ≤ (2 * α * β) ^ p := Real.rpow_nonneg (by positivity) _
  induction n with
  | zero =>
    intro c _
    simp [I_Phi, I_gw_zero]
  | succ n ih =>
    intro c hc
    have hper : ∀ (c : ℤ), ∀ t : ℤ, (fun v => I_Phi α β n c v ^ p) (t + ((2 ^ n : ℕ) : ℤ)) =
        (fun v => I_Phi α β n c v ^ p) t := by
      intro c t; simp only; rw [I_Phi_per]
    have hNpos : 0 < 2 ^ n := by positivity
    rw [pow_succ', I_sum_range_two_mul]
    push_cast
    -- even `v`
    have hA : ∑ x ∈ range (2 ^ n), I_Phi α β (n + 1) c (2 * (x : ℤ)) ^ p ≤
        (1 + (2 * α * β) ^ p) ^ n := by
      have hle : ∀ x ∈ range (2 ^ n), I_Phi α β (n + 1) c (2 * (x : ℤ)) ^ p ≤
          β ^ 2 * I_Phi α β n c x ^ p + α ^ 2 * I_Phi α β n c (3 * x + (1 - c) / 2) ^ p := by
        intro x _
        rw [I_Phi_even n c x hc]
        have := hconv.2 (x := I_Phi α β n c x) (y := I_Phi α β n c (3 * x + (1 - c) / 2))
          (Set.mem_Ici.mpr (I_Phi_nonneg hα hβ _ _ _)) (Set.mem_Ici.mpr (I_Phi_nonneg hα hβ _ _ _))
          (sq_nonneg β) (sq_nonneg α) (by linarith)
        simpa [smul_eq_mul] using this
      refine le_trans (sum_le_sum hle) ?_
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      have hs := I_sum_affine (2 ^ n) hNpos (fun v => I_Phi α β n c v ^ p) (hper c) 3 ((1 - c) / 2)
        (I_coprime_three n)
      try simp only at hs
      rw [hs]
      have := ih c hc
      have e : β ^ 2 * ∑ x ∈ range (2 ^ n), I_Phi α β n c ↑x ^ p +
          α ^ 2 * ∑ x ∈ range (2 ^ n), I_Phi α β n c ↑x ^ p =
          ∑ x ∈ range (2 ^ n), I_Phi α β n c ↑x ^ p := by
        rw [← add_mul, add_comm, h1, one_mul]
      rw [e]; exact this
    -- odd `v`
    have hB : ∑ x ∈ range (2 ^ n), I_Phi α β (n + 1) c (2 * (x : ℤ) + 1) ^ p ≤
        (2 * α * β) ^ p * (1 + (2 * α * β) ^ p) ^ n := by
      set c' := c * 3 ^ (2 ^ n - 1) with hc'
      have hc'odd : c' % 2 = 1 := by
        have : Odd c' := Odd.mul (Int.odd_iff.mpr hc) (Odd.pow (by decide))
        exact Int.odd_iff.mp this
      have h3odd : (3 * c) % 2 = 1 := by omega
      have hle : ∀ x ∈ range (2 ^ n), I_Phi α β (n + 1) c (2 * (x : ℤ) + 1) ^ p ≤
          (2 * α * β) ^ p / 2 * (I_Phi α β n (3 * c) (3 * x + 2) ^ p +
            I_Phi α β n c' (x + ((c + 1) / 2 - 2 * c')) ^ p) := by
        intro x _
        rw [I_Phi_odd n c x hc]
        set X := I_Phi α β n (3 * c) (3 * x + 2)
        set Y := I_Phi α β n c' (x + ((c + 1) / 2 - 2 * c'))
        have hY : I_Phi α β n (c * 3 ^ (2 ^ n - 1)) (x + (c + 1) / 2 - 2 * (c * 3 ^ (2 ^ n - 1))) = Y := by
          simp only [Y, hc']; congr 1; ring
        rw [hY]
        have hX0 : 0 ≤ X := I_Phi_nonneg hα hβ _ _ _
        have hY0 : 0 ≤ Y := I_Phi_nonneg hα hβ _ _ _
        have hconv2 := hconv.2 (x := X) (y := Y) (Set.mem_Ici.mpr hX0) (Set.mem_Ici.mpr hY0)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
        simp only [smul_eq_mul] at hconv2
        rw [show α * β * (X + Y) = (2 * α * β) * (1 / 2 * X + 1 / 2 * Y) by ring,
          Real.mul_rpow (by positivity) (by positivity)]
        calc (2 * α * β) ^ p * (1 / 2 * X + 1 / 2 * Y) ^ p ≤
            (2 * α * β) ^ p * (1 / 2 * X ^ p + 1 / 2 * Y ^ p) :=
              mul_le_mul_of_nonneg_left hconv2 hr
          _ = (2 * α * β) ^ p / 2 * (X ^ p + Y ^ p) := by ring
      refine le_trans (sum_le_sum hle) ?_
      rw [← mul_sum, sum_add_distrib]
      have hs1 := I_sum_affine (2 ^ n) hNpos (fun v => I_Phi α β n (3 * c) v ^ p) (hper (3 * c)) 3 2
        (I_coprime_three n)
      have hs2 := I_sum_shift (2 ^ n) hNpos (fun v => I_Phi α β n c' v ^ p) (hper c') ((c + 1) / 2 - 2 * c')
      try simp only at hs1 hs2
      rw [hs1, hs2]
      have i1 := ih (3 * c) h3odd
      have i2 := ih c' hc'odd
      have : (2 * α * β) ^ p / 2 * (∑ v ∈ range (2 ^ n), I_Phi α β n (3 * c) v ^ p +
          ∑ v ∈ range (2 ^ n), I_Phi α β n c' v ^ p) ≤
          (2 * α * β) ^ p / 2 * ((1 + (2 * α * β) ^ p) ^ n + (1 + (2 * α * β) ^ p) ^ n) :=
        mul_le_mul_of_nonneg_left (add_le_add i1 i2) (by positivity)
      linarith
    calc _ ≤ (1 + (2 * α * β) ^ p) ^ n + (2 * α * β) ^ p * (1 + (2 * α * β) ^ p) ^ n := add_le_add hA hB
      _ = (1 + (2 * α * β) ^ p) ^ (n + 1) := by ring

end Phi

end Collatz.M1
