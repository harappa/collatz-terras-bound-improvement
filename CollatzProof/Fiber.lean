import CollatzProof.Defs

/-!
# An auxiliary lemma: bounds on fibers and images when stopping at the minimum of the coefficient walk

From an earlier development in the source repository, not a result of the paper; the paper uses `Collatz.terras_inj` of this file (Lemma 3.1 of the paper). The comparison `y_i ≥ y_j` of the heights `y_i = λ o_i - i` is expressed by the integer inequality
`3^{o_j} 2^i ≤ 3^{o_i} 2^j`.
-/

namespace Collatz

/-- The height at time `j` is at most every height at times `0 ≤ i ≤ j` (the word ends at a minimum at time `j`). -/
def MinEnd (n j : ℕ) : Prop := ∀ i ≤ j, 3 ^ (o n j) * 2 ^ i ≤ 3 ^ (o n i) * 2 ^ j

lemma o_succ_le (n j : ℕ) : o n (j + 1) ≤ o n j + 1 := by
  simp only [o]; split_ifs <;> omega

lemma o_le_succ (n j : ℕ) : o n j ≤ o n (j + 1) := by
  simp only [o]; split_ifs <;> omega

/-- Invariant: for `k ≤ J`, `3 · 3^{o_J} c_k ≤ o_k 3^{o_k} 2^J` (under `MinEnd n J`). -/
lemma c_inv (n J : ℕ) (hJ : MinEnd n J) :
    ∀ k ≤ J, 3 * 3 ^ (o n J) * c n k ≤ o n k * 3 ^ (o n k) * 2 ^ J := by
  intro k
  induction k with
  | zero => intro _; simp [c]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hmin := hJ k (by omega)
    by_cases h : T^[k] n % 2 = 1
    · have ho : o n (k + 1) = o n k + 1 := by simp [o, h]
      have hc : c n (k + 1) = 3 * c n k + 2 ^ k := by simp [c, h]
      rw [ho, hc]
      calc 3 * 3 ^ o n J * (3 * c n k + 2 ^ k)
          = 3 * (3 * 3 ^ o n J * c n k) + 3 * (3 ^ o n J * 2 ^ k) := by ring
        _ ≤ 3 * (o n k * 3 ^ o n k * 2 ^ J) + 3 * (3 ^ o n k * 2 ^ J) := by gcongr
        _ = (o n k + 1) * 3 ^ (o n k + 1) * 2 ^ J := by ring
    · have ho : o n (k + 1) = o n k := by simp [o, h]
      have hc : c n (k + 1) = c n k := by simp [c, h]
      rw [ho, hc]; exact ih'

/-- If `MinEnd n j`, then `3 c_j ≤ o_j 2^j`. -/
theorem c_bound (n j : ℕ) (h : MinEnd n j) : 3 * c n j ≤ o n j * 2 ^ j := by
  have := c_inv n j h j le_rfl
  have hpos : 0 < 3 ^ o n j := by positivity
  have : 3 ^ o n j * (3 * c n j) ≤ 3 ^ o n j * (o n j * 2 ^ j) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this hpos

/-- Always `c_j + 2^j ≤ 3^{o_j} 2^j`. -/
theorem c_add_le (n j : ℕ) : c n j + 2 ^ j ≤ 3 ^ (o n j) * 2 ^ j := by
  induction j with
  | zero => simp [c, o]
  | succ j ih =>
    by_cases h : T^[j] n % 2 = 1
    · have ho : o n (j + 1) = o n j + 1 := by simp [o, h]
      have hc : c n (j + 1) = 3 * c n j + 2 ^ j := by simp [c, h]
      rw [ho, hc]
      have : 2 ^ j ≤ 3 ^ o n j * 2 ^ j := by
        have : 1 ≤ 3 ^ o n j := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      have hX : 0 ≤ 3 ^ o n j * 2 ^ j := Nat.zero_le _
      calc 3 * c n j + 2 ^ j + 2 ^ (j + 1) = 3 * (c n j + 2 ^ j) := by rw [pow_succ]; ring
        _ ≤ 3 * (3 ^ o n j * 2 ^ j) := by omega
        _ ≤ 3 ^ (o n j + 1) * 2 ^ (j + 1) := by rw [pow_succ, pow_succ]; nlinarith
    · have ho : o n (j + 1) = o n j := by simp [o, h]
      have hc : c n (j + 1) = c n j := by simp [c, h]
      rw [ho, hc]
      have : 2 ^ j ≤ 3 ^ o n j * 2 ^ j := by
        have : 1 ≤ 3 ^ o n j := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      calc c n j + 2 ^ (j + 1) = (c n j + 2 ^ j) + 2 ^ j := by rw [pow_succ]; ring
        _ ≤ 3 ^ o n j * 2 ^ j + 3 ^ o n j * 2 ^ j := by omega
        _ = 3 ^ o n j * 2 ^ (j + 1) := by rw [pow_succ]; ring

/-- Image bound: if `N < 2^t` and `j ≤ t`, then `T^j(N) < 3^{o_j} 2^{t+1-j}`. -/
theorem iter_lt (N t j : ℕ) (hN : N < 2 ^ t) (hj : j ≤ t) :
    T^[j] N < 3 ^ (o N j) * 2 ^ (t + 1 - j) := by
  have hd := dual N j
  have hc := c_add_le N j
  have h2 : 2 ^ (t + 1 - j) * 2 ^ j = 2 ^ (t + 1) := by
    rw [← pow_add]; congr 1; omega
  have h3 : (2:ℕ) ^ j ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hj
  have hpos : 0 < 2 ^ j := by positivity
  have key : 2 ^ j * T^[j] N < 2 ^ j * (3 ^ o N j * 2 ^ (t + 1 - j)) := by
    rw [hd]
    have e : 2 ^ j * (3 ^ o N j * 2 ^ (t + 1 - j)) = 3 ^ o N j * 2 ^ (t + 1) := by
      rw [← h2]; ring
    rw [e, pow_succ]
    have h1 : 1 ≤ 3 ^ o N j := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left key

end Collatz

namespace Collatz

/-- A finite set of natural numbers whose pairwise differences are all at most `d` has at most `d + 1` elements. -/
lemma card_le_of_diam (S : Finset ℕ) (d : ℕ) (h : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → b - a ≤ d) :
    S.card ≤ d + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · set m := S.min' hne
    have hsub : S ⊆ Finset.Icc m (m + d) := by
      intro x hx
      have hmx : m ≤ x := S.min'_le x hx
      have := h m (S.min'_mem hne) x hx hmx
      rw [Finset.mem_Icc]; omega
    calc S.card ≤ (Finset.Icc m (m + d)).card := Finset.card_le_card hsub
      _ = d + 1 := by rw [Nat.card_Icc]; omega

/-- Auxiliary lemma (fiber): the number of `N` with `o_j = L`, ending at a minimum at time `j`, and `T^j N = M` is at most `L 2^j / 3^{L+1} + 1`. -/
theorem fiber_card (j L M : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ S, o N j = L ∧ MinEnd N j ∧ T^[j] N = M) :
    S.card ≤ L * 2 ^ j / 3 ^ (L + 1) + 1 := by
  apply card_le_of_diam
  intro a ha b hb hab
  obtain ⟨hoa, hma, hTa⟩ := hS a ha
  obtain ⟨hob, hmb, hTb⟩ := hS b hb
  have da := dual a j
  have db := dual b j
  rw [hTa, hoa] at da
  rw [hTb, hob] at db
  have ca := c_bound a j hma
  rw [hoa] at ca
  -- 3^L a + c_a = 3^L b + c_b, and b ≥ a, give 3^L (b - a) = c_a - c_b ≤ c_a
  have key : 3 ^ L * (b - a) ≤ c a j := by
    have : 3 ^ L * b + c b j = 3 ^ L * a + c a j := by rw [← db, ← da]
    have hb' : 3 ^ L * (b - a) = 3 ^ L * b - 3 ^ L * a := Nat.mul_sub _ _ _
    omega
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc (b - a) * 3 ^ (L + 1) = 3 * (3 ^ L * (b - a)) := by ring
    _ ≤ 3 * c a j := by omega
    _ ≤ L * 2 ^ j := ca

/-- The number of odd steps and the additive term are determined by the parity sequence alone. -/
lemma o_c_eq_of_parity (N N' t : ℕ) (hpar : ∀ i < t, T^[i] N % 2 = T^[i] N' % 2) :
    ∀ k ≤ t, o N k = o N' k ∧ c N k = c N' k := by
  intro k
  induction k with
  | zero => intro _; simp [o, c]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hp := hpar k (by omega)
    constructor
    · simp only [o, hp, h1]
    · simp only [c, hp, h2]

/-- Terras injectivity: two numbers in `[0, 2^t)` whose parities agree over the first `t` steps are equal. -/
theorem terras_inj (t N N' : ℕ) (hN : N < 2 ^ t) (hN' : N' < 2 ^ t)
    (hpar : ∀ i < t, T^[i] N % 2 = T^[i] N' % 2) : N = N' := by
  obtain ⟨ho, hc⟩ := o_c_eq_of_parity N N' t hpar t le_rfl
  have d1 := dual N t
  have d2 := dual N' t
  have h1 : 3 ^ o N t * N + c N t ≡ 3 ^ o N t * N' + c N t [MOD 2 ^ t] := by
    have e1 : (3 ^ o N t * N + c N t) % 2 ^ t = 0 := by rw [← d1]; simp
    have e2 : (3 ^ o N t * N' + c N t) % 2 ^ t = 0 := by rw [ho, hc, ← d2]; simp
    unfold Nat.ModEq; rw [e1, e2]
  have h2 := Nat.ModEq.add_right_cancel' _ h1
  have hcop : Nat.gcd (2 ^ t) (3 ^ o N t) = 1 := by
    exact Nat.Coprime.pow _ _ (by norm_num)
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime hcop h2) hN hN'

end Collatz
