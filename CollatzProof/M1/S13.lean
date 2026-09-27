import CollatzProof.M1.Counting
import CollatzProof.M1.Compat

/-! # §13: the height condition (HGT) (Bugeaud (2002) is used as a hypothesis)

Auxiliary lemmas (prefix `J_`): numerical values of logarithms, the lifting-the-exponent lemma (2-adic valuation of `3^M ∓ 1`),
reduction by the gcd, the dependent case (`a₀/b₀ = ±3^k`), the application of Bugeaud's theorem (Lemma 13.1A), and finally Proposition 13.2. -/

namespace Collatz.M1

/-! ## Auxiliary: numerical values of logarithms and "sufficiently large `q`" -/

/-- `19 log 2 < 12 log 3` (`2^19 < 3^12`). -/
theorem J_log3_lo : 19 * Real.log 2 < 12 * Real.log 3 := by
  have h := Real.log_lt_log (by norm_num : (0:ℝ) < 2 ^ 19) (by norm_num : (2:ℝ) ^ 19 < 3 ^ 12)
  simpa [Real.log_pow] using h

/-- `5 log 3 < 8 log 2` (`3^5 < 2^8`). -/
theorem J_log3_hi : 5 * Real.log 3 < 8 * Real.log 2 := by
  have h := Real.log_lt_log (by norm_num : (0:ℝ) < 3 ^ 5) (by norm_num : (3:ℝ) ^ 5 < 2 ^ 8)
  simpa [Real.log_pow] using h

/-- For sufficiently large `q`, `2000 + 2000 log q ≤ 0.089 q`. -/
theorem J_ev : ∃ q0 : ℕ, ∀ q : ℕ, q0 ≤ q →
    1 ≤ (q:ℝ) ∧ 2000 + 2000 * Real.log q ≤ 0.089 * (q:ℝ) := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (0.089 / 4000) * x := by
    have := Real.isLittleO_log_id_atTop.def (show (0:ℝ) < 0.089 / 4000 by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx0] at hx
    exact (le_abs_self _).trans hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 50000 ≤ x := Filter.eventually_ge_atTop _
  obtain ⟨q0, hq0⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (h1.and h2))
  refine ⟨q0, fun q hq => ?_⟩
  obtain ⟨ha, hb⟩ := hq0 q hq
  refine ⟨by linarith, by linarith⟩

/-! ## Auxiliary: 2-adic valuations (the lifting-the-exponent lemma) -/

/-- `3^M ≡ 1` or `3 (mod 8)`. -/
theorem J_pow3_mod8 (M : ℕ) : (3:ℤ) ^ M % 8 = 1 ∨ (3:ℤ) ^ M % 8 = 3 := by
  induction M with
  | zero => left; norm_num
  | succ n ih =>
    rw [pow_succ, Int.mul_emod]
    rcases ih with h | h <;> rw [h] <;> norm_num

/-- `3^{2k} ≡ 1 (mod 8)`. -/
theorem J_pow3_even_mod8 (k : ℕ) : (3:ℤ) ^ (2 * k) % 8 = 1 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, Int.mul_emod, ih]; norm_num

/-- If the 2-adic valuation is at least `k`, then `2^k` divides. -/
theorem J_dvd_of_le {z : ℤ} {k : ℕ} (h : k ≤ padicValInt 2 z) : (2:ℤ) ^ k ∣ z :=
  (padicValInt_dvd_iff (p := 2) k z).2 (Or.inr h)

/-- The 2-adic valuation `v` of `3^M − σ` (`σ = ±1`, nonzero) satisfies `2^v ≤ 4M + 4` (lifting the exponent). -/
theorem J_v2_pow3_sub (M : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hne : (3:ℤ) ^ M - σ ≠ 0) :
    2 ^ padicValInt 2 ((3:ℤ) ^ M - σ) ≤ 4 * M + 4 := by
  rcases hσ with rfl | rfl
  · -- 3^M − 1
    have hM : M ≠ 0 := by rintro rfl; simp at hne
    rcases Nat.even_or_odd M with hev | hod
    · have h1 := padicValNat.pow_two_sub_one (x := 3) (by norm_num) (by norm_num) hM hev
      have h4 : padicValNat 2 (3 + 1) = 2 := by
        rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
      have h2 : padicValNat 2 (3 - 1) = 1 := by
        rw [show (3 - 1 : ℕ) = 2 by norm_num]; simp
      have hcast : ((3:ℤ) ^ M - 1) = ((3 ^ M - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; ring
      rw [hcast, padicValInt.of_nat]
      have hv : padicValNat 2 (3 ^ M - 1) = padicValNat 2 M + 2 := by omega
      rw [hv, pow_add]
      have hd : 2 ^ padicValNat 2 M ≤ M :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hM) pow_padicValNat_dvd
      omega
    · obtain ⟨k, rfl⟩ := hod
      have h8 : ¬ (2:ℤ) ^ 2 ∣ (3:ℤ) ^ (2 * k + 1) - 1 := by
        intro hd
        have h0 := J_pow3_even_mod8 k
        have : (3:ℤ) ^ (2 * k + 1) % 8 = 3 := by
          rw [pow_succ, Int.mul_emod, h0]; norm_num
        omega
      have hv : padicValInt 2 ((3:ℤ) ^ (2 * k + 1) - 1) ≤ 1 := by
        by_contra hc
        exact h8 (J_dvd_of_le (by omega))
      calc 2 ^ padicValInt 2 ((3:ℤ) ^ (2 * k + 1) - 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hv
        _ ≤ _ := by omega
  · -- 3^M + 1
    have h8 : ¬ (2:ℤ) ^ 3 ∣ (3:ℤ) ^ M - -1 := by
      intro hd
      rcases J_pow3_mod8 M with h | h <;> omega
    have hv : padicValInt 2 ((3:ℤ) ^ M - -1) ≤ 2 := by
      by_contra hc
      exact h8 (J_dvd_of_le (by omega))
    calc 2 ^ padicValInt 2 ((3:ℤ) ^ M - -1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hv
      _ ≤ _ := by omega

/-- Multiplying by an odd number does not change the 2-adic valuation. -/
theorem J_v2_mul_odd {w z : ℤ} (hw : Odd w) : padicValInt 2 (w * z) = padicValInt 2 z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [padicValInt.mul hw0 hz, padicValInt.eq_zero_of_not_dvd, zero_add]
  rw [← Int.not_even_iff_odd, even_iff_two_dvd] at hw
  exact_mod_cast hw

/-- The 2-adic valuation `v` of `3^x − σ3^y` (`σ = ±1`, nonzero) satisfies `2^v ≤ 4(x + y) + 4`. -/
theorem J_v2_pow3_pair (x y : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hne : (3:ℤ) ^ x - σ * 3 ^ y ≠ 0) :
    2 ^ padicValInt 2 ((3:ℤ) ^ x - σ * 3 ^ y) ≤ 4 * (x + y) + 4 := by
  have h3 : ∀ k : ℕ, Odd ((3:ℤ) ^ k) := fun k => Odd.pow (by decide)
  rcases le_total y x with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    have he : (3:ℤ) ^ (y + m) - σ * 3 ^ y = 3 ^ y * (3 ^ m - σ) := by ring
    rw [he] at hne ⊢
    rw [J_v2_mul_odd (h3 y)]
    have hne' : (3:ℤ) ^ m - σ ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hne; exact hne rfl
    have := J_v2_pow3_sub m σ hσ hne'
    omega
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    have hodd : Odd (-σ * 3 ^ x) := by
      rcases hσ with rfl | rfl
      · simpa using h3 x
      · simpa using h3 x
    have he : (3:ℤ) ^ x - σ * 3 ^ (x + m) = (-σ * 3 ^ x) * (3 ^ m - σ) := by
      rcases hσ with rfl | rfl <;> ring
    rw [he] at hne ⊢
    rw [J_v2_mul_odd hodd]
    have hne' : (3:ℤ) ^ m - σ ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hne; exact hne rfl
    have := J_v2_pow3_sub m σ hσ hne'
    omega

/-! ## Auxiliary: reduction to lowest terms and parity -/

/-- If `2^n ∣ gN` (`g ≥ 1`, `N ≠ 0`), then `2^n ≤ g 2^{v_2(N)}`. -/
theorem J_dvd_bound (g : ℕ) (hg : 0 < g) (N : ℤ) (hN : N ≠ 0) (n : ℕ)
    (h : (2:ℤ) ^ n ∣ (g:ℤ) * N) : 2 ^ n ≤ g * 2 ^ padicValInt 2 N := by
  have hg0 : (g:ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 := (padicValInt_dvd_iff (p := 2) n ((g:ℤ) * N)).1 (by exact_mod_cast h)
  rcases h1 with h1 | h1
  · exact absurd h1 (mul_ne_zero hg0 hN)
  rw [padicValInt.mul hg0 hN, padicValInt.of_nat] at h1
  have hd : 2 ^ padicValNat 2 g ≤ g := Nat.le_of_dvd hg pow_padicValNat_dvd
  calc 2 ^ n ≤ 2 ^ (padicValNat 2 g + padicValInt 2 N) := Nat.pow_le_pow_right (by norm_num) h1
    _ = 2 ^ padicValNat 2 g * 2 ^ padicValInt 2 N := pow_add _ _ _
    _ ≤ g * 2 ^ padicValInt 2 N := Nat.mul_le_mul_right _ hd

/-- For coprime integers with `3^L b₀ − a₀` even, `a₀`, `b₀` are both odd. -/
theorem J_odd_of_coprime (L : ℕ) (a0 b0 : ℤ) (hg : Int.gcd a0 b0 = 1)
    (h2 : (2:ℤ) ∣ 3 ^ L * b0 - a0) : Odd a0 ∧ Odd b0 := by
  have h3 : Odd ((3:ℤ) ^ L) := Odd.pow (by decide)
  have hnot : ¬ ((2:ℤ) ∣ a0 ∧ (2:ℤ) ∣ b0) := by
    rintro ⟨ha, hb⟩
    have := Int.dvd_coe_gcd ha hb
    rw [hg] at this; norm_num at this
  rw [← even_iff_two_dvd] at h2
  by_cases ha : Even a0
  · have hb : Even b0 := by
      have : Even (3 ^ L * b0) := by
        have := h2.add ha; simpa using this
      rcases Int.even_mul.1 this with h | h
      · exact absurd h (Int.not_even_iff_odd.2 h3)
      · exact h
    exact absurd ⟨even_iff_two_dvd.1 ha, even_iff_two_dvd.1 hb⟩ hnot
  · have ha' : Odd a0 := Int.not_even_iff_odd.1 ha
    refine ⟨ha', ?_⟩
    by_contra hb
    have hb' : Even b0 := Int.not_odd_iff_even.1 hb
    have : Even (3 ^ L * b0 - a0 + a0) := by
      simpa using (Int.even_mul.2 (Or.inr hb'))
    exact ha ((Int.even_add.1 this).1 h2)

/-! ## Auxiliary: the multiplicatively dependent case -/

/-- A prime `p ≠ 3` does not divide `3^k`. -/
theorem J_not_dvd_pow3 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (k : ℕ) : ¬ p ∣ 3 ^ k := by
  intro h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))

/-- A nonzero integer with no prime factor other than 3 is `±3^i`. -/
theorem J_abs_pow3 (z : ℤ) (hz : z ≠ 0) (h : ∀ p : ℕ, p.Prime → p ≠ 3 → ¬ (p:ℤ) ∣ z) :
    ∃ i : ℕ, (3:ℤ) ^ i = |z| := by
  have hn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz
  have := Nat.eq_prime_pow_of_unique_prime_dvd hn (p := 3) (fun {d} hd hdvd => by
    by_contra hd3
    exact h d hd hd3 (Int.natCast_dvd.2 hdvd))
  obtain ⟨k, hk⟩ : ∃ k, z.natAbs = 3 ^ k := ⟨_, this⟩
  refine ⟨k, ?_⟩
  rw [← Int.natCast_natAbs, hk]; push_cast; rfl

/-- The dependent case: if `a₀/(3^e b₀)` and 9 are multiplicatively dependent, then `|a₀| = 3^i`, `|b₀| = 3^j`, and
the 2-adic valuation `v` of `3^L b₀ − a₀ ≠ 0` satisfies `2^v ≤ 4(L + j + i) + 4`. -/
theorem J_dep (L e : ℕ) (a0 b0 : ℤ) (hg : Int.gcd a0 b0 = 1) (ha : a0 ≠ 0) (hb : b0 ≠ 0)
    (hdep : ¬ MulIndep 9 ((a0 : ℚ) / ((3:ℚ) ^ e * b0))) :
    ∃ i j : ℕ, (3:ℤ) ^ i = |a0| ∧ (3:ℤ) ^ j = |b0| ∧
      (3 ^ L * b0 - a0 ≠ 0 → 2 ^ padicValInt 2 (3 ^ L * b0 - a0) ≤ 4 * (L + j + i) + 4) := by
  set r2 : ℚ := (a0 : ℚ) / ((3:ℚ) ^ e * b0) with hr2
  have ha' : (a0 : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b0 : ℚ) ≠ 0 := by exact_mod_cast hb
  have h3e : ((3:ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hr0 : r2 ≠ 0 := div_ne_zero ha' (mul_ne_zero h3e hb')
  unfold MulIndep at hdep
  push Not at hdep
  obtain ⟨k1, k2, hk, hk0⟩ := hdep
  have hk2 : k2 ≠ 0 := by
    intro h0
    rw [h0, zpow_zero, mul_one, zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at hk
    exact hk0 hk h0
  -- The valuation at primes other than 3 is 0
  have hval : ∀ p : ℕ, p.Prime → p ≠ 3 → padicValInt p a0 = padicValInt p b0 := by
    intro p hp hp3
    have := Fact.mk hp
    have h9 : padicValRat p 9 = 0 := by
      rw [show (9:ℚ) = ((3 ^ 2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (J_not_dvd_pow3 hp hp3 2)]; rfl
    have h1 := congrArg (padicValRat p) hk
    rw [padicValRat.mul (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hr0),
      cpt_padicValRat_zpow (by norm_num : (9:ℚ) ≠ 0), cpt_padicValRat_zpow hr0, h9, padicValRat.one,
      mul_zero, zero_add] at h1
    have h2 : padicValRat p r2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hk2
      · exact h
    rw [hr2, padicValRat.div ha' (mul_ne_zero h3e hb'), padicValRat.mul h3e hb',
      cpt_padicValRat_pow (by norm_num : (3:ℚ) ≠ 0), show (3:ℚ) = ((3:ℕ):ℚ) by norm_num,
      padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (fun h => J_not_dvd_pow3 hp hp3 1 (by simpa using h))] at h2
    rw [show (a0 : ℚ) = ((a0:ℤ):ℚ) from rfl, padicValRat.of_int,
      show (b0 : ℚ) = ((b0:ℤ):ℚ) from rfl, padicValRat.of_int] at h2
    push_cast at h2
    omega
  have hnd : ∀ p : ℕ, p.Prime → p ≠ 3 → ¬ (p:ℤ) ∣ a0 ∧ ¬ (p:ℤ) ∣ b0 := by
    intro p hp hp3
    have := Fact.mk hp
    have hcop : ¬ ((p:ℤ) ∣ a0 ∧ (p:ℤ) ∣ b0) := by
      rintro ⟨h1, h2⟩
      have := Int.dvd_coe_gcd h1 h2
      rw [hg] at this
      have h1 : p ∣ 1 := by exact_mod_cast this
      exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
    have hv := hval p hp hp3
    constructor
    · intro h1
      have : 1 ≤ padicValInt p a0 := by
        rcases (padicValInt_dvd_iff 1 a0).1 (by simpa using h1) with h | h
        · exact absurd h ha
        · exact h
      have h2 : (p:ℤ) ∣ b0 := by
        have := (padicValInt_dvd_iff (p := p) 1 b0).2 (Or.inr (by omega)); simpa using this
      exact hcop ⟨h1, h2⟩
    · intro h2
      have : 1 ≤ padicValInt p b0 := by
        rcases (padicValInt_dvd_iff 1 b0).1 (by simpa using h2) with h | h
        · exact absurd h hb
        · exact h
      have h1 : (p:ℤ) ∣ a0 := by
        have := (padicValInt_dvd_iff (p := p) 1 a0).2 (Or.inr (by omega)); simpa using this
      exact hcop ⟨h1, h2⟩
  obtain ⟨i, hi⟩ := J_abs_pow3 a0 ha (fun p hp hp3 => (hnd p hp hp3).1)
  obtain ⟨j, hj⟩ := J_abs_pow3 b0 hb (fun p hp hp3 => (hnd p hp hp3).2)
  refine ⟨i, j, hi, hj, fun hN => ?_⟩
  have hsa : a0 = 3 ^ i ∨ a0 = -3 ^ i := by
    rcases abs_choice a0 with h | h <;> [left; right] <;> linarith
  have hsb : b0 = 3 ^ j ∨ b0 = -3 ^ j := by
    rcases abs_choice b0 with h | h <;> [left; right] <;> linarith
  -- `3^L b₀ − a₀ = τ (3^{L+j} − σ 3^i)`
  obtain ⟨τ, σ, hτ, hσ, hE⟩ : ∃ τ σ : ℤ, (τ = 1 ∨ τ = -1) ∧ (σ = 1 ∨ σ = -1) ∧
      3 ^ L * b0 - a0 = τ * ((3:ℤ) ^ (L + j) - σ * 3 ^ i) := by
    rcases hsa with rfl | rfl <;> rcases hsb with rfl | rfl
    · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by ring⟩
    · exact ⟨-1, -1, Or.inr rfl, Or.inr rfl, by ring⟩
    · exact ⟨1, -1, Or.inl rfl, Or.inr rfl, by ring⟩
    · exact ⟨-1, 1, Or.inr rfl, Or.inl rfl, by ring⟩
  have hτo : Odd τ := by rcases hτ with rfl | rfl <;> decide
  rw [hE, J_v2_mul_odd hτo]
  have hne : (3:ℤ) ^ (L + j) - σ * 3 ^ i ≠ 0 := by
    intro h0; rw [hE, h0, mul_zero] at hN; exact hN rfl
  have := J_v2_pow3_pair (L + j) i σ hσ hne
  omega

/-! ## Auxiliary: application of Bugeaud's theorem (Lemma 13.1A) -/

/-- The 2-adic valuation of an odd number is 0. -/
theorem J_v2_odd {z : ℤ} (hz : Odd z) : padicValInt 2 z = 0 := by
  simpa using J_v2_mul_odd (z := 1) hz

/-- The body of Lemma 13.1A (application of Bugeaud's theorem with `m = 8`, `μ = 4`, `g = 1`, `x₁/y₁ = 9`, `x₂/y₂ = a₀/(3^e b₀)`,
`b₁ = ⌊L/2⌋`, `b₂ = 1`, `A₁ = 9`, `A₂ = e^u`): if `a₀`, `b₀` are odd, `8 ∣ 3^L b₀ − a₀ ≠ 0`, `a₀/(3^e b₀)` and 9 are multiplicatively
independent (`e = L mod 2`), and `u` satisfies the height condition, then `⌊v_2(3^L b₀ − a₀)/3⌋` is at most Bugeaud's right-hand side. -/
theorem J_bug (hBug : BugeaudHyp) (L : ℕ) (hL : 2 ≤ L) (a0 b0 : ℤ) (ha : Odd a0) (hb : Odd b0)
    (h8 : (8:ℤ) ∣ 3 ^ L * b0 - a0) (hN : 3 ^ L * b0 - a0 ≠ 0)
    (hind : MulIndep 9 ((a0 : ℚ) / ((3:ℚ) ^ (L % 2) * b0)))
    (u : ℝ) (hu8 : Real.log 8 ≤ u) (hua : Real.log |(a0:ℝ)| ≤ u)
    (hub : Real.log (3 * |(b0:ℝ)|) ≤ u) :
    ((padicValInt 2 (3 ^ L * b0 - a0) / 3 : ℕ) : ℝ) ≤
      53.6 * ((1:ℕ):ℝ) / (Real.log 8) ^ 4 *
        (max (Real.log (((L / 2 : ℕ) : ℝ) / u + ((1:ℕ):ℝ) / Real.log 9) + Real.log (Real.log 8) + 0.64)
          (4 * Real.log 8)) ^ 2 * Real.log 9 * u := by
  set e := L % 2 with he
  set b1 := L / 2 with hb1
  have hLe : L = 2 * b1 + e := (Nat.div_add_mod L 2).symm
  set B : ℤ := 3 ^ e * b0 with hB
  have hBo : Odd B := (Odd.pow (by decide)).mul hb
  have hB0 : B ≠ 0 := by rintro h; rw [h] at hBo; exact absurd hBo (by decide)
  have ha0 : a0 ≠ 0 := by rintro rfl; exact absurd ha (by decide)
  set N : ℤ := 3 ^ L * b0 - a0 with hNdef
  set r2 : ℚ := ((a0:ℤ):ℚ) / ((B:ℤ):ℚ) with hr2
  have hr2' : (a0 : ℚ) / ((3:ℚ) ^ e * b0) = r2 := by rw [hr2, hB]; push_cast; ring
  rw [hr2'] at hind
  have hBq : ((B:ℤ):ℚ) ≠ 0 := by exact_mod_cast hB0
  have haq : ((a0:ℤ):ℚ) ≠ 0 := by exact_mod_cast ha0
  have hr0 : r2 ≠ 0 := div_ne_zero haq hBq
  have hr1 : r2 ≠ 1 := by
    intro h
    have := hind 0 1 (by simp [h])
    exact absurd this.2 one_ne_zero
  -- `3^L b₀ = 9^{b₁} B`
  have h3L : (3:ℤ) ^ L * b0 = 9 ^ b1 * B := by
    rw [hLe, hB, pow_add, pow_mul]; norm_num; ring
  -- (H2): `8 ∣ a₀ − B`
  have h8' : (2:ℤ) ^ 3 ∣ a0 - B := by
    have h9 : (8:ℤ) ∣ 9 ^ b1 - 1 := by
      simpa using sub_dvd_pow_sub_pow (9:ℤ) 1 b1
    have : a0 - B = (9 ^ b1 - 1) * B - N := by rw [hNdef, h3L]; ring
    rw [this]; norm_num
    exact dvd_sub (dvd_mul_of_dvd_left h9 _) h8
  have haB : a0 - B ≠ 0 := by
    intro h0; apply hr1; rw [hr2, show a0 = B by linarith]; exact div_self hBq
  have hvaB : 3 ≤ padicValInt 2 (a0 - B) := by
    rcases (padicValInt_dvd_iff (p := 2) 3 (a0 - B)).1 (by exact_mod_cast h8') with h | h
    · exact absurd h haB
    · exact h
  have hvB : padicValInt 2 B = 0 := J_v2_odd hBo
  have hva : padicValInt 2 a0 = 0 := J_v2_odd ha
  -- Sizes of the numerator and the denominator
  have hdiv : r2 = Rat.divInt a0 B := Rat.intCast_div_eq_divInt a0 B
  have hnum : |r2.num| ≤ |a0| := by
    have h1 : r2.num ∣ a0 := by rw [hdiv]; exact Rat.num_dvd a0 hB0
    exact Int.le_of_dvd (abs_pos.2 ha0) ((abs_dvd_abs _ _).2 h1)
  have hden : (r2.den : ℤ) ≤ 3 * |b0| := by
    have h1 : (r2.den : ℤ) ∣ B := by rw [hdiv]; exact Rat.den_dvd a0 B
    have h2 := Int.le_of_dvd (abs_pos.2 hB0) ((dvd_abs _ _).2 h1)
    have h3 : |B| ≤ 3 * |b0| := by
      rw [hB, abs_mul, abs_pow]
      have : |(3:ℤ)| ^ e ≤ 3 := by
        have : e ≤ 1 := by omega
        interval_cases e <;> norm_num
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    linarith
  have hnum0 : r2.num ≠ 0 := Rat.num_ne_zero.2 hr0
  have hu0 : 0 < u := lt_of_lt_of_le (Real.log_pos (by norm_num)) hu8
  have key := hBug 9 r2 1 b1 1 9 (Real.exp u) (by norm_num) hr0 (by norm_num) (by norm_num)
    (by unfold v2q; rw [show (9:ℚ) = ((9:ℕ):ℚ) by norm_num, padicValRat.of_nat,
          padicValNat.eq_zero_of_not_dvd (by norm_num)]; rfl)
    (by unfold v2q; rw [hr2, padicValRat.div haq hBq, padicValRat.of_int, padicValRat.of_int, hva, hvB]; rfl)
    le_rfl rfl
    (by unfold v2q; rw [show (9:ℚ) ^ 1 - 1 = ((2 ^ 3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
          padicValNat.prime_pow]; norm_num)
    (by
      unfold v2q
      have : r2 ^ 1 - 1 = ((a0 - B : ℤ) : ℚ) / ((B:ℤ):ℚ) := by
        rw [pow_one, hr2]; field_simp; push_cast; ring
      rw [this, padicValRat.div (by exact_mod_cast haB) hBq, padicValRat.of_int, padicValRat.of_int, hvB]
      push_cast; omega)
    (by omega) le_rfl (by omega) hind (by norm_num) (Real.one_lt_exp_iff.2 hu0)
    (by simp) (by simp; positivity) (Real.log_le_log (by norm_num) (by norm_num))
    (by
      rw [Real.log_exp]
      refine le_trans (Real.log_le_log (by positivity) ?_) hua
      exact_mod_cast hnum)
    (by
      rw [Real.log_exp]
      refine le_trans (Real.log_le_log (by exact_mod_cast r2.den_pos) ?_) hub
      exact_mod_cast hden)
    (by rw [Real.log_exp]; exact hu8)
  rw [Real.log_exp] at key
  -- `v₈(9^{b₁} − r₂) = ⌊v_2(N)/3⌋`
  have hx : (9:ℚ) ^ b1 - r2 ^ 1 = Rat.divInt N B := by
    rw [← Rat.intCast_div_eq_divInt, pow_one, hr2, hNdef]
    field_simp
    have : ((3 ^ L * b0 - a0 : ℤ) : ℚ) = ((9 ^ b1 * B - a0 : ℤ) : ℚ) := by rw [h3L]
    push_cast at this ⊢
    rw [this]
  have hv8 : v8 ((9:ℚ) ^ b1 - r2 ^ 1) = ((padicValInt 2 N / 3 : ℕ) : ℤ) := by
    rw [hx]
    set x := Rat.divInt N B with hxdef
    have hxden : padicValNat 2 x.den = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h2
      have h1 : (x.den : ℤ) ∣ B := by rw [hxdef]; exact Rat.den_dvd N B
      have : (2:ℤ) ∣ B := dvd_trans (by exact_mod_cast h2) h1
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
  rw [hv8] at key
  convert key using 1

/-! ## Proposition 13.2 -/

set_option maxHeartbeats 1000000 in
/-- Proposition 13.2: let `1 < s/q ≤ 1.94`, `0 < c_D ≤ 9×10^{−4}`, `D = ⌊c_D q⌋`, `0 ≤ h_L ≤ 10^{−8}q`. For sufficiently large `q`
(the threshold does not depend on `L`, `s`), if `a ≡ 3^L b (mod 2^{q+D})` and `(a, b) ≠ (0, 0)`, then `max(|a|, |b|) ≥ q2^D(q2^{h_L} + 1)`.

**Correction of the statement**: the argument order of `LatticeCond` is `q L D H` (`L` comes first, following the order of `variable (q s L)`). The skeleton
had `LatticeCond q ⌊c_D q⌋₊ L _`, which means `a ≡ 3^{⌊c_D q⌋} b (mod 2^{q+L})` and differs from Proposition 13.2 of the manuscript
(moreover it is false for small `c_D`: `(a, b) = (3^D, 1)` is a counterexample). It was corrected to `LatticeCond q L ⌊c_D q⌋₊ _`, as in the manuscript. -/
theorem hgt (hBug : BugeaudHyp) (cD : ℝ) (hcD0 : 0 < cD) (hcD1 : cD ≤ 9e-4) :
    ∃ q0 : ℕ, ∀ s q L : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 → 0 ≤ hL s L →
      hL s L ≤ 1e-8 * q →
      LatticeCond q L ⌊cD * q⌋₊ (q * 2 ^ ⌊cD * q⌋₊ * (q * (2:ℝ) ^ hL s L + 1)) := by
  obtain ⟨q0, hq0⟩ := J_ev
  refine ⟨q0, fun s q L hq hs1 hs2 hL0 hL1 a b hab hmod => ?_⟩
  obtain ⟨hq1, hmaster⟩ := hq0 q hq
  set D := ⌊cD * q⌋₊ with hD
  set h := hL s L with hh
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hl3a := J_log3_lo
  have hl3b := J_log3_hi
  set ℓ2 := Real.log 2 with hl2
  set ℓ3 := Real.log 3 with hl3
  -- Basic facts about `q`, `s`, `L`
  have hq0' : (0:ℝ) < q := by linarith
  have hsq : (q:ℝ) < s := by rwa [one_lt_div hq0'] at hs1
  have hsq2 : (s:ℝ) ≤ 1.94 * q := by rwa [div_le_iff₀ hq0'] at hs2
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
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
  have hDl : (D:ℝ) * ℓ2 ≤ 9e-4 * (q * ℓ2) := by
    have : (D:ℝ) ≤ 9e-4 * q := by nlinarith only [hDr, hcD1, hq0']
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
  -- Divide out the gcd: `a = a₀g`, `b = b₀g`, `gcd(a₀, b₀) = 1`
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
  · -- `a₀ = 3^L b₀`: contradiction, since `|a| ≥ 3^L > H`
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
  · -- `N₀ ≠ 0`: `v = v_2(N₀)` satisfies `2^{q+D} ≤ g2^v < H2^v`, i.e. `q log 2 < W + v log 2`
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
    by_cases hind : MulIndep 9 ((a0 : ℚ) / ((3:ℚ) ^ (L % 2) * b0))
    · -- Independent case: Bugeaud's theorem (Lemma 13.1A). `A₂ = e^u`, `u = max(log(3H), 6.6×10^{−4}q)`
      set u : ℝ := max (Real.log (3 * (2 ^ D * H'))) (6.6e-4 * q) with hu
      have hl3p : 0 < ℓ3 := by linarith
      have hl8 : Real.log 8 = 3 * ℓ2 := by
        rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow, hl2]; norm_num
      have hl9 : Real.log 9 = 2 * ℓ3 := by
        rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.log_pow, hl3]; norm_num
      have hu66 : 6.6e-4 * (q:ℝ) ≤ u := le_max_right _ _
      have hu8 : Real.log 8 ≤ u := by
        rw [hl8]; refine le_trans ?_ hu66
        nlinarith only [hl2b, hmaster, hlogq]
      have hu0 : 0 < u := by linarith
      have hHM : ∀ z : ℤ, |z| ≤ M → z ≠ 0 → Real.log (3 * |(z:ℝ)|) ≤ u := by
        intro z hz hz0
        refine le_trans (Real.log_le_log (by positivity) ?_) (le_max_left _ _)
        have : ((|z|:ℤ):ℝ) ≤ (M:ℝ) := by exact_mod_cast hz
        rw [Int.cast_abs] at this
        linarith
      have hua : Real.log |(a0:ℝ)| ≤ u := by
        refine le_trans (Real.log_le_log (by positivity) ?_) (hHM a0 hMa ha0)
        have : 0 ≤ |(a0:ℝ)| := abs_nonneg _
        linarith
      have hub : Real.log (3 * |(b0:ℝ)|) ≤ u := hHM b0 hMb hb0
      have key := J_bug hBug L hL2 a0 b0 hao hbo h8 hN0 hind u hu8 hua hub
      rw [← hN0def, ← hv, hl8, hl9, Nat.cast_one] at key
      -- `max{⋯} = 4 log 8`
      set b1r : ℝ := ((L / 2 : ℕ) : ℝ) with hb1r
      have hb1 : b1r ≤ L / 2 := Nat.cast_div_le
      have hb10 : 0 ≤ b1r := by positivity
      have hbu : b1r / u ≤ 928.3 := by
        rw [div_le_iff₀ hu0]
        nlinarith only [hb1, hLq, hu66, hq0']
      have h19 : 1 / (2 * ℓ3) ≤ 0.46 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hl3a, hl2a]
      have hbp : 0 < b1r / u + 1 / (2 * ℓ3) := by positivity
      have hZ : Real.log (b1r / u + 1 / (2 * ℓ3)) + Real.log (3 * ℓ2) + 0.64 ≤ 4 * (3 * ℓ2) := by
        have h1 : (b1r / u + 1 / (2 * ℓ3)) * (3 * ℓ2) ≤ 2 ^ 11 := by
          nlinarith only [hbu, h19, hl2b, hl2p]
        have h2 := Real.log_le_log (by positivity) h1
        rw [Real.log_mul hbp.ne' (by positivity), Real.log_pow] at h2
        push_cast at h2
        linarith
      rw [max_eq_right hZ] at key
      have key2 : ((v / 3 : ℕ) : ℝ) ≤ (15436.8 / 81) * (ℓ3 * u / ℓ2 ^ 2) := by
        refine le_of_le_of_eq key ?_
        field_simp
        ring
      -- `v log 2 ≤ 914.78 u + 2 log 2`
      have hv3le : (v:ℝ) ≤ 3 * ((v / 3 : ℕ) : ℝ) + 2 := by
        have : v ≤ 3 * (v / 3) + 2 := by omega
        exact_mod_cast this
      have hT : ℓ3 * u / ℓ2 ^ 2 * ℓ2 ≤ 1.6 * u := by
        rw [show ℓ3 * u / ℓ2 ^ 2 * ℓ2 = ℓ3 * u / ℓ2 by field_simp]
        rw [div_le_iff₀ hl2p]
        nlinarith only [hl3b, hu0]
      have hvl : (v:ℝ) * ℓ2 ≤ 3 * (15436.8 / 81) * (ℓ3 * u / ℓ2 ^ 2 * ℓ2) + 2 * ℓ2 := by
        have h1 : (v:ℝ) ≤ 3 * ((15436.8 / 81) * (ℓ3 * u / ℓ2 ^ 2)) + 2 := by linarith
        have h2 := mul_le_mul_of_nonneg_right h1 hl2p.le
        linarith
      -- `u ≤ log 3 + 6.6×10^{−4}q + W`
      have hule : u ≤ ℓ3 + 6.6e-4 * q + W := by
        apply max_le
        · rw [Real.log_mul (by norm_num) hHpos.ne', hlogH]
          nlinarith only [hDl, hX2]
        · linarith
      nlinarith only [hmainlog, hvl, hT, hule, hWle, hhl, hX1, hX2, hmaster, hlogq, hl3b, hl2b, hl2p]
    · -- Dependent case (`a₀/b₀ = ±3^k`): `2^v ≤ 4(L + j + i) + 4` by lifting the exponent
      obtain ⟨i, j, hi, hj, hbd⟩ := J_dep L (L % 2) a0 b0 hgcd ha0 hb0 hind
      have hvb := hbd hN0
      rw [← hN0def, ← hv] at hvb
      have hpow : ∀ k : ℕ, (3:ℤ) ^ k ≤ M → (k:ℝ) < 2 ^ D * H' := by
        intro k hk
        have h1 : (k:ℝ) < 3 ^ k := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
        have h2 : ((3:ℝ) ^ k) ≤ (M:ℝ) := by exact_mod_cast hk
        linarith
      have hir := hpow i (hi ▸ hMa)
      have hjr := hpow j (hj ▸ hMb)
      have hH1 : H' ≤ 2 ^ D * H' := le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
      have hvr : (2:ℝ) ^ v ≤ 16 * (2 ^ D * H') := by
        have : ((2 ^ v : ℕ) : ℝ) ≤ ((4 * (L + j + i) + 4 : ℕ) : ℝ) := by exact_mod_cast hvb
        push_cast at this
        nlinarith only [this, hLq, hir, hjr, hH'2, hH1]
      have := Real.log_le_log (by positivity) hvr
      rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), hlogH,
        show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
      push_cast at this
      nlinarith only [this, hmainlog, hWle, hhl, hDl, hX1, hmaster, hlogq, hl2b]

end Collatz.M1
