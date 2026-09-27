import CollatzProof.M1.I_BC

/-!
# Auxiliary results for §12.1: weights on the survival set, upper bounds on the autocorrelation `r_E` and its shallow part `r^{sh}` (the core of Lemma 12.1 and Corollary 12.2)

- `I_sa = √ρ_c`, `I_sb = √(1−ρ_c)`. `g_q = I_gw I_sa I_sb q` is `√Q_q`.
- If `z ∈ E` (it survives for length `q` from height `y ≥ 0`), then `1 ≤ 2^{t*y}(2f)^q Q_q(z)` (the first line of the proof of Lemma 12.1 (i), `I_E_weight`).
- `r_E(v) = #{(z, z') ∈ E² | z' + v ≡ z (2^q)} ≤ C·BC_q(v)`, where `BC_q(v) = Φ_q(1, v)` (`I_rE_le`).
- `r^{sh}(v) = 2^{j₀−q}#{(z, z') ∈ E² | z' + v ≡ z (2^{j₀})} ≤ C((1+r_c)/2)^{q−j₀}` (Lemma 12.1 (ii)(iii), `I_rSh_le`).
-/

namespace Collatz.M1

open Finset

/-! ## Constants -/

/-- `√ρ_c`. -/
noncomputable def I_sa : ℝ := Real.sqrt rhoc
/-- `√(1 − ρ_c)`. -/
noncomputable def I_sb : ℝ := Real.sqrt (1 - rhoc)

lemma I_rhoc_pos : 0 < rhoc := by linarith [rhoc_bounds.1]
lemma I_rhoc_lt_one : rhoc < 1 := by linarith [rhoc_bounds.2]
lemma I_sa_nonneg : 0 ≤ I_sa := Real.sqrt_nonneg _
lemma I_sb_nonneg : 0 ≤ I_sb := Real.sqrt_nonneg _
lemma I_sa_mul_self : I_sa * I_sa = rhoc := Real.mul_self_sqrt I_rhoc_pos.le
lemma I_sb_mul_self : I_sb * I_sb = 1 - rhoc := Real.mul_self_sqrt (by linarith [I_rhoc_lt_one])
lemma I_sq_add : I_sa ^ 2 + I_sb ^ 2 = 1 := by
  rw [sq, sq, I_sa_mul_self, I_sb_mul_self]; ring
lemma I_two_sa_sb : 2 * I_sa * I_sb = rc := by
  unfold rc I_sa I_sb; rw [mul_assoc, ← Real.sqrt_mul I_rhoc_pos.le]
lemma I_sum_sq : (I_sa + I_sb) ^ 2 = 1 + rc := by
  rw [← I_two_sa_sb]; nlinarith [I_sq_add]

lemma I_rc_nonneg : 0 ≤ rc := by rw [← I_two_sa_sb]; have := I_sa_nonneg; have := I_sb_nonneg; positivity

/-- `g_q(x)² = Q_q(x)`. -/
lemma I_gq_sq (n : ℕ) (x : ℤ) : I_gw I_sa I_sb n x * I_gw I_sa I_sb n x = I_gw rhoc (1 - rhoc) n x := by
  rw [I_gw_mul, I_sa_mul_self, I_sb_mul_self]

/-! ## Weights on the survival set -/

/-- The first line of the proof of Lemma 12.1 (i): if `z ∈ E`, then `1 ≤ 2^{t*y}(2f)^q Q_q(z)`. -/
lemma I_E_weight (q : ℕ) (hq : 1 ≤ q) (y : ℝ) (z : ℕ) (hz : z ∈ Eset q y) :
    1 ≤ (2 : ℝ) ^ (tstar * y) * (2 * ff) ^ q * I_gw rhoc (1 - rhoc) q z := by
  simp only [Eset, Finset.mem_filter] at hz
  obtain ⟨_, hsurv⟩ := hz
  have hh := hsurv q hq le_rfl
  unfold hw at hh
  set o := ones (pw z q) q with ho_def
  rw [I_gw_nat, Finset.prod_ite, prod_const, prod_const]
  have ho : (univ.filter (fun i : Fin q => T^[(i : ℕ)] z % 2 = 1)).card = o := by
    rw [ho_def]; unfold ones pw; congr 1; ext i; simp
  have ho' : (univ.filter (fun i : Fin q => ¬ T^[(i : ℕ)] z % 2 = 1)).card = q - o := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin q)))
      (p := fun i : Fin q => T^[(i : ℕ)] z % 2 = 1)
    rw [card_univ, Fintype.card_fin] at this; omega
  have hol : o ≤ q := by
    rw [← ho]; exact le_trans (card_filter_le _ _) (by simp)
  rw [ho, ho']
  obtain ⟨_, hρ, h1ρ⟩ := lemma17
  have hf : 0 < ff := by unfold ff; positivity
  have e1 : 2 * ff * rhoc = (2 : ℝ) ^ (tstar * aa) := by rw [hρ]; field_simp
  have e2 : 2 * ff * (1 - rhoc) = (2 : ℝ) ^ (-tstar) := by rw [h1ρ]; field_simp
  have hsplit : (2 * ff) ^ q * (rhoc ^ o * (1 - rhoc) ^ (q - o)) =
      (2 * ff * rhoc) ^ o * (2 * ff * (1 - rhoc)) ^ (q - o) := by
    have : (2 * ff) ^ q = (2 * ff) ^ o * (2 * ff) ^ (q - o) := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_pow (2 * ff) rhoc, mul_pow (2 * ff) (1 - rhoc)]; ring
  rw [mul_assoc, hsplit, e1, e2, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  apply Real.one_le_rpow (by norm_num)
  have ht : 0 < tstar := by linarith [tstar_bounds.1]
  have hcast : ((q - o : ℕ) : ℝ) = (q : ℝ) - o := by rw [Nat.cast_sub hol]
  rw [hcast]
  have : tstar * y + (tstar * aa * o + -tstar * ((q : ℝ) - o)) = tstar * (y + lam * o - q) := by
    unfold aa; ring
  rw [this]
  exact mul_nonneg ht.le hh

/-- The `√C` form: `1 ≤ √(2^{t*y}(2f)^q) · g_q(z)`. -/
lemma I_E_weight_sqrt (q : ℕ) (hq : 1 ≤ q) (y : ℝ) (z : ℕ) (hz : z ∈ Eset q y) :
    1 ≤ Real.sqrt ((2 : ℝ) ^ (tstar * y) * (2 * ff) ^ q) * I_gw I_sa I_sb q z := by
  have h := I_E_weight q hq y z hz
  have hC : 0 ≤ (2 : ℝ) ^ (tstar * y) * (2 * ff) ^ q := by
    have hf : 0 < ff := by unfold ff; positivity
    positivity
  have hg : 0 ≤ I_gw I_sa I_sb q z := I_gw_nonneg I_sa_nonneg I_sb_nonneg _ _
  have hsq : (Real.sqrt ((2 : ℝ) ^ (tstar * y) * (2 * ff) ^ q) * I_gw I_sa I_sb q z) ^ 2 =
      (2 : ℝ) ^ (tstar * y) * (2 * ff) ^ q * I_gw rhoc (1 - rhoc) q z := by
    rw [mul_pow, Real.sq_sqrt hC, sq, I_gq_sq]
  have h0 : 0 ≤ Real.sqrt ((2 : ℝ) ^ (tstar * y) * (2 * ff) ^ q) * I_gw I_sa I_sb q z :=
    mul_nonneg (Real.sqrt_nonneg _) hg
  nlinarith

/-! ## `Σ_y g_j(y) g_j(y+v) ≤ 1` and the cross sum -/

lemma I_sum_gq_sq (j : ℕ) : ∑ y ∈ range (2 ^ j), I_gw I_sa I_sb j y * I_gw I_sa I_sb j y = 1 := by
  simp_rw [I_gq_sq]
  have := I_class_sum rhoc (1 - rhoc) j 0 (Nat.zero_le _) 0
  simp only [pow_zero, one_dvd, ite_true, I_gw_zero, one_mul, Nat.sub_zero] at this
  rw [this]; ring

lemma I_auto_le_one (j : ℕ) (v : ℤ) :
    ∑ y ∈ range (2 ^ j), I_gw I_sa I_sb j y * I_gw I_sa I_sb j (y + v) ≤ 1 := by
  have hper : ∀ x : ℤ, (fun t => I_gw I_sa I_sb j t * I_gw I_sa I_sb j t) (x + ((2 ^ j : ℕ) : ℤ)) =
      (fun t => I_gw I_sa I_sb j t * I_gw I_sa I_sb j t) x := by
    intro x; simp only
    have := I_gw_per (α := I_sa) (β := I_sb) j x 1
    push_cast; simp at this; rw [this]
  have hs := I_sum_shift (2 ^ j) (by positivity) (fun t => I_gw I_sa I_sb j t * I_gw I_sa I_sb j t)
    hper v
  have h2 : ∑ y ∈ range (2 ^ j), I_gw I_sa I_sb j y * I_gw I_sa I_sb j (y + v) ≤
      ∑ y ∈ range (2 ^ j), (I_gw I_sa I_sb j y * I_gw I_sa I_sb j y +
        I_gw I_sa I_sb j (y + v) * I_gw I_sa I_sb j (y + v)) / 2 := by
    apply sum_le_sum; intro y _
    nlinarith [sq_nonneg (I_gw I_sa I_sb j y - I_gw I_sa I_sb j (y + v))]
  rw [← sum_div, sum_add_distrib, hs, I_sum_gq_sq] at h2
  linarith

/-- Cross sum: if `j ≤ q`, then `Σ_{z<2^q} g_q(z) g_j(z+v) ≤ (α+β)^{q−j}`. -/
lemma I_cross_le (q j : ℕ) (hj : j ≤ q) (v : ℤ) :
    ∑ z ∈ range (2 ^ q), I_gw I_sa I_sb q z * I_gw I_sa I_sb j (z + v) ≤ (I_sa + I_sb) ^ (q - j) := by
  have hH : ∀ x k : ℤ, I_gw I_sa I_sb j (x + 2 ^ j * k + v) = I_gw I_sa I_sb j (x + v) := by
    intro x k; rw [show x + 2 ^ j * k + v = x + v + 2 ^ j * k by ring, I_gw_per]
  rw [I_sum_group q j (fun z => I_gw I_sa I_sb q z) (fun x => I_gw I_sa I_sb j (x + v)) hH]
  simp_rw [I_class_sum I_sa I_sb q j hj]
  have hs : ∑ y ∈ range (2 ^ j), I_gw I_sa I_sb j (↑y + v) * (I_gw I_sa I_sb j ↑y * (I_sa + I_sb) ^ (q - j)) =
      (I_sa + I_sb) ^ (q - j) * ∑ y ∈ range (2 ^ j), I_gw I_sa I_sb j y * I_gw I_sa I_sb j (y + v) := by
    rw [mul_sum]; apply sum_congr rfl; intro y _; ring
  rw [hs]
  have hpos : 0 ≤ (I_sa + I_sb) ^ (q - j) := by have := I_sa_nonneg; have := I_sb_nonneg; positivity
  calc _ ≤ (I_sa + I_sb) ^ (q - j) * 1 := mul_le_mul_of_nonneg_left (I_auto_le_one j v) hpos
    _ = _ := mul_one _

/-! ## Upper bound on the number of pairs -/

/-- Number of pairs: if `E ⊆ [0, 2^q)` and `1 ≤ K g_q(z)` for `z ∈ E`, then
`#{(z, z') ∈ E² | 2^j ∣ z' − z + v} ≤ K²(α+β)^{q−j} Σ_{z'<2^q} g_q(z') g_j(z'+v)`. -/
lemma I_pair_le (q j : ℕ) (hj : j ≤ q) (E : Finset ℕ) (hE : E ⊆ range (2 ^ q)) (K : ℝ)
    (hw : ∀ z ∈ E, 1 ≤ K * I_gw I_sa I_sb q z) (v : ℤ) :
    ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ j ∣ (z' : ℤ) - z + v then (1 : ℝ) else 0) ≤
      K ^ 2 * (I_sa + I_sb) ^ (q - j) *
        ∑ z' ∈ range (2 ^ q), I_gw I_sa I_sb q z' * I_gw I_sa I_sb j (z' + v) := by
  set g : ℤ → ℝ := I_gw I_sa I_sb q with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => I_gw_nonneg I_sa_nonneg I_sb_nonneg _ _
  set F : ℕ → ℕ → ℝ := fun z z' =>
    if (2 : ℤ) ^ j ∣ (z' : ℤ) - z + v then K ^ 2 * (g z * g z') else 0 with hF
  have hF0 : ∀ z z', 0 ≤ F z z' := by
    intro z z'; simp only [hF]; split_ifs
    · exact mul_nonneg (sq_nonneg K) (mul_nonneg (hg0 _) (hg0 _))
    · exact le_rfl
  have step1 : ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ j ∣ (z' : ℤ) - z + v then (1 : ℝ) else 0) ≤
      ∑ z ∈ E, ∑ z' ∈ E, F z z' := by
    apply sum_le_sum; intro z hz; apply sum_le_sum; intro z' hz'
    simp only [hF]; split_ifs
    · have := one_le_mul_of_one_le_of_one_le (hw z hz) (hw z' hz')
      calc (1 : ℝ) ≤ K * g z * (K * g z') := this
        _ = K ^ 2 * (g z * g z') := by ring
    · exact le_rfl
  have step2 : ∑ z ∈ E, ∑ z' ∈ E, F z z' ≤ ∑ z ∈ range (2 ^ q), ∑ z' ∈ range (2 ^ q), F z z' := by
    calc ∑ z ∈ E, ∑ z' ∈ E, F z z' ≤ ∑ z ∈ E, ∑ z' ∈ range (2 ^ q), F z z' :=
          sum_le_sum fun z _ => sum_le_sum_of_subset_of_nonneg hE fun z' _ _ => hF0 z z'
      _ ≤ ∑ z ∈ range (2 ^ q), ∑ z' ∈ range (2 ^ q), F z z' :=
          sum_le_sum_of_subset_of_nonneg hE fun z _ _ => sum_nonneg fun z' _ => hF0 z z'
  have step3 : ∑ z ∈ range (2 ^ q), ∑ z' ∈ range (2 ^ q), F z z' =
      K ^ 2 * ∑ z' ∈ range (2 ^ q), g z' *
        ∑ z ∈ range (2 ^ q), (if (2 : ℤ) ^ j ∣ (z : ℤ) - ((z' : ℤ) + v) then g z else 0) := by
    rw [sum_comm, mul_sum]; apply sum_congr rfl; intro z' _
    rw [mul_sum, mul_sum]; apply sum_congr rfl; intro z _
    simp only [hF]
    have hiff : (2 : ℤ) ^ j ∣ (z' : ℤ) - z + v ↔ (2 : ℤ) ^ j ∣ (z : ℤ) - ((z' : ℤ) + v) := by
      rw [show (z' : ℤ) - z + v = ((z' : ℤ) + v) - z by ring, dvd_sub_comm]
    by_cases h : (2 : ℤ) ^ j ∣ (z' : ℤ) - z + v
    · rw [if_pos h, if_pos (hiff.mp h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; ring
  have step4 : ∀ z' : ℕ, ∑ z ∈ range (2 ^ q), (if (2 : ℤ) ^ j ∣ (z : ℤ) - ((z' : ℤ) + v) then g z else 0) =
      I_gw I_sa I_sb j ((z' : ℤ) + v) * (I_sa + I_sb) ^ (q - j) := by
    intro z'; exact I_class_sum I_sa I_sb q j hj _
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ = K ^ 2 * (I_sa + I_sb) ^ (q - j) *
          ∑ z' ∈ range (2 ^ q), I_gw I_sa I_sb q z' * I_gw I_sa I_sb j (z' + v) := by
      simp_rw [step4, mul_sum]; apply sum_congr rfl; intro z' _; simp only [hg]; ring

/-- `r_E(v) ≤ K² BC_q(v)`, where `BC_q(v) = Φ_q(1, v)`. -/
lemma I_rE_le (q : ℕ) (E : Finset ℕ) (hE : E ⊆ range (2 ^ q)) (K : ℝ)
    (hw : ∀ z ∈ E, 1 ≤ K * I_gw I_sa I_sb q z) (v : ℤ) :
    ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ q ∣ (z' : ℤ) - z + v then (1 : ℝ) else 0) ≤
      K ^ 2 * I_Phi I_sa I_sb q 1 v := by
  have := I_pair_le q q le_rfl E hE K hw v
  rw [Nat.sub_self, pow_zero, mul_one] at this
  refine le_trans this (le_of_eq ?_)
  unfold I_Phi; congr 1; apply sum_congr rfl; intro z _; rw [one_mul]

/-- `r^{sh}(v) ≤ K²((1+r_c)/2)^{q−j₀}`. -/
lemma I_rSh_le (q j0 : ℕ) (hj0 : j0 ≤ q) (E : Finset ℕ) (hE : E ⊆ range (2 ^ q)) (K : ℝ)
    (hw : ∀ z ∈ E, 1 ≤ K * I_gw I_sa I_sb q z) (v : ℤ) :
    (2 : ℝ) ^ j0 / 2 ^ q * ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ j0 ∣ (z' : ℤ) - z + v then (1 : ℝ) else 0) ≤
      K ^ 2 * ((1 + rc) / 2) ^ (q - j0) := by
  have h1 := I_pair_le q j0 hj0 E hE K hw v
  have h2 := I_cross_le q j0 hj0 v
  have hs0 : 0 ≤ (I_sa + I_sb) ^ (q - j0) := by have := I_sa_nonneg; have := I_sb_nonneg; positivity
  have h3 : ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ j0 ∣ (z' : ℤ) - z + v then (1 : ℝ) else 0) ≤
      K ^ 2 * ((I_sa + I_sb) ^ (q - j0) * (I_sa + I_sb) ^ (q - j0)) := by
    refine le_trans h1 ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hs0) (sq_nonneg K)
  have hpow : (I_sa + I_sb) ^ (q - j0) * (I_sa + I_sb) ^ (q - j0) = (1 + rc) ^ (q - j0) := by
    rw [← mul_pow, ← sq, I_sum_sq]
  rw [hpow] at h3
  have hq2 : (2 : ℝ) ^ j0 / 2 ^ q = (1 / 2) ^ (q - j0) := by
    rw [one_div_pow, div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
    congr 1; omega
  rw [hq2]
  calc (1 / 2 : ℝ) ^ (q - j0) * _ ≤ (1 / 2) ^ (q - j0) * (K ^ 2 * (1 + rc) ^ (q - j0)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = K ^ 2 * ((1 + rc) / 2) ^ (q - j0) := by rw [div_pow, div_pow, one_pow]; ring

end Collatz.M1
