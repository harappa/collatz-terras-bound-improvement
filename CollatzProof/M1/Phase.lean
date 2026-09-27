import CollatzProof.M1.Counting
import CollatzProof.M1.G_Riesz
import CollatzProof.M1.Compat

/-!
# §8: phase tools (Lemmas 8.1–8.5)

Used in common by §9 (the outer shells) and §10 (shell 0 and the inner shells). The slice `(L, P)`, the tail `τ` and the swap block `k` are fixed.
-/

namespace Collatz.M1

open Finset

/-! ## Auxiliary: inverses in `ZMod` -/

/-- `2^m` is a unit modulo `3^n`: `2^m (2^m)^{−1} = 1`. -/
theorem G_two_pow_mul_inv (m n : ℕ) : ((2 : ZMod (3 ^ n)) ^ m) * ((2 : ZMod (3 ^ n)) ^ m)⁻¹ = 1 := by
  have h : Nat.Coprime (2 ^ m) (3 ^ n) := Nat.Coprime.pow _ _ (by norm_num)
  have := ZMod.coe_mul_inv_eq_one (2 ^ m) h
  push_cast at this; exact this

/-- `3^n` is a unit modulo `2^m`: `3^n (3^n)^{−1} = 1`. -/
theorem G_three_pow_mul_inv (m n : ℕ) : ((3 : ZMod (2 ^ m)) ^ n) * ((3 : ZMod (2 ^ m)) ^ n)⁻¹ = 1 := by
  have h : Nat.Coprime (3 ^ n) (2 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  have := ZMod.coe_mul_inv_eq_one (3 ^ n) h
  push_cast at this; exact this

/-- If `x = 2^q y` modulo `3^n`, then `x (2^{d+q})^{−1} = y (2^d)^{−1}`. -/
theorem G_inv2_shift (n d q : ℕ) (x y : ZMod (3 ^ n)) (h : x = 2 ^ q * y) :
    x * ((2 : ZMod (3 ^ n)) ^ (d + q))⁻¹ = y * ((2 : ZMod (3 ^ n)) ^ d)⁻¹ := by
  have hu : IsUnit ((2 : ZMod (3 ^ n)) ^ (d + q)) := IsUnit.of_mul_eq_one _ (G_two_pow_mul_inv (d + q) n)
  apply hu.mul_right_cancel
  have h1 := G_two_pow_mul_inv (d + q) n
  have h2 := G_two_pow_mul_inv d n
  rw [pow_add] at h1 ⊢
  linear_combination x * h1 - y * 2 ^ q * h2 + h

/-- If `n ≤ L`, then `3^L = 0` modulo `3^n`. -/
theorem G_three_pow_zero (n L : ℕ) (hn : n ≤ L) : ((3 : ZMod (3 ^ n)) ^ L) = 0 := by
  rw [← Nat.sub_add_cancel hn, pow_add]
  have : ((3 : ZMod (3 ^ n)) ^ n) = 0 := by exact_mod_cast ZMod.natCast_self (3 ^ n)
  rw [this, mul_zero]

/-- Lemma 8.1 (reciprocity law): `2^m⟨2^{−m}⟩_{3^n} + 3^n⟨3^{−n}⟩_{2^m} = 1 + 2^m 3^n` (`m, n ≥ 1`). -/
theorem recip (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    2 ^ m * inv2mod m n 1 + 3 ^ n * (((3 : ZMod (2 ^ m)) ^ n)⁻¹).val = 1 + 2 ^ m * 3 ^ n := by
  set a := inv2mod m n 1 with ha
  set b := (((3 : ZMod (2 ^ m)) ^ n)⁻¹).val with hb
  have ha_lt : a < 3 ^ n := ZMod.val_lt _
  have hb_lt : b < 2 ^ m := ZMod.val_lt _
  have hA : ((2 ^ m * a : ℕ) : ZMod (3 ^ n)) = 1 := by
    rw [ha, inv2mod]; push_cast
    rw [ZMod.natCast_zmod_val, one_mul, G_two_pow_mul_inv]
  have hB : ((3 ^ n * b : ℕ) : ZMod (2 ^ m)) = 1 := by
    rw [hb]; push_cast
    rw [ZMod.natCast_zmod_val, G_three_pow_mul_inv]
  have h3 : 3 ≤ 3 ^ n := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, mul_zero, Nat.cast_zero] at hA
      have := (ZMod.natCast_eq_natCast_iff' 0 1 (3 ^ n)).mp (by simpa using hA)
      rw [Nat.zero_mod, Nat.one_mod_eq_one.mpr (by omega)] at this
      omega
    · exact h
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero, Nat.cast_zero] at hB
      have := (ZMod.natCast_eq_natCast_iff' 0 1 (2 ^ m)).mp (by simpa using hB)
      rw [Nat.zero_mod, Nat.one_mod_eq_one.mpr (by omega)] at this
      omega
    · exact h
  -- it is 1 modulo 3^n and modulo 2^m
  have hx3 : (2 ^ m * a + 3 ^ n * b) ≡ 1 [MOD 3 ^ n] := by
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast at hA ⊢
    rw [hA]
    have : ((3 : ZMod (3 ^ n)) ^ n) = 0 := by exact_mod_cast ZMod.natCast_self (3 ^ n)
    rw [this]; simp
  have hx2 : (2 ^ m * a + 3 ^ n * b) ≡ 1 [MOD 2 ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast at hB ⊢
    rw [hB]
    have : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ m)
    rw [this]; simp
  have hcop : Nat.Coprime (2 ^ m) (3 ^ n) := Nat.Coprime.pow _ _ (by norm_num)
  have hx : (2 ^ m * a + 3 ^ n * b) ≡ 1 [MOD 2 ^ m * 3 ^ n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hx2, hx3⟩
  set M := 2 ^ m * 3 ^ n with hM
  set x := 2 ^ m * a + 3 ^ n * b with hxdef
  have hM6 : 6 ≤ M := by rw [hM]; nlinarith
  have hxlo : 2 ≤ x := by rw [hxdef]; nlinarith
  have hxhi : x < 2 * M := by
    rw [hxdef, hM]
    have : 2 ^ m * a ≤ 2 ^ m * (3 ^ n - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 3 ^ n * b ≤ 3 ^ n * (2 ^ m - 1) := Nat.mul_le_mul_left _ (by omega)
    have e1 : 2 ^ m * (3 ^ n - 1) = 2 ^ m * 3 ^ n - 2 ^ m := by rw [Nat.mul_sub_one]
    have e2 : 3 ^ n * (2 ^ m - 1) = 2 ^ m * 3 ^ n - 3 ^ n := by rw [Nat.mul_sub_one, mul_comm]
    have : 2 ^ m ≤ 2 ^ m * 3 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
    have : 3 ^ n ≤ 2 ^ m * 3 ^ n := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hmod : x % M = 1 := by
    have := hx; unfold Nat.ModEq at this; rw [this]; exact Nat.one_mod_eq_one.mpr (by omega)
  have hdiv := Nat.div_add_mod x M
  rw [hmod] at hdiv
  have hq1 : x / M = 1 := by
    have hlt : x / M < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
    have hge : 1 ≤ x / M := by
      rcases Nat.eq_zero_or_pos (x / M) with h | h
      · rw [h, mul_zero, zero_add] at hdiv; omega
      · exact h
    omega
  rw [hq1, mul_one] at hdiv
  omega

/-- `κ(N) = (3^L ξ_N − N)/2^q` (an integer). -/
noncomputable def kappaN (q L : ℕ) (N : ℤ) : ℤ := (3 ^ L * (xiN q L N : ℤ) - N) / 2 ^ q

/-- `2^q ∣ 3^L ξ_N − N`. -/
theorem G_xiN_dvd (q L : ℕ) (N : ℤ) : (2 ^ q : ℤ) ∣ 3 ^ L * (xiN q L N : ℤ) - N := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (3 ^ L * (xiN q L N : ℤ) - N) (2 ^ q)).mp
  push_cast at h; apply h
  rw [xiN, ZMod.natCast_zmod_val, mul_left_comm, G_three_pow_mul_inv, mul_one, sub_self]

/-- `N = 3^L ξ_N − 2^q κ(N)`. -/
theorem kappaN_spec (q L : ℕ) (N : ℤ) : N = 3 ^ L * (xiN q L N : ℤ) - 2 ^ q * kappaN q L N := by
  rw [kappaN, Int.mul_ediv_cancel' (G_xiN_dvd q L N)]; ring

/-- Given `ξ ∈ [0, 2^q)` and `κ ∈ ℤ`, setting `N = 3^L ξ − 2^q κ` gives `ξ_N = ξ` and `κ(N) = κ`. -/
theorem xiN_kappaN_of (q L : ℕ) (ξ : ℕ) (hξ : ξ < 2 ^ q) (κ : ℤ) :
    xiN q L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) = ξ ∧ kappaN q L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) = κ := by
  have h1 : xiN q L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) = ξ := by
    rw [xiN]; push_cast
    have : ((2 : ZMod (2 ^ q)) ^ q) = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ q)
    rw [this, zero_mul, sub_zero, mul_comm, ← mul_assoc, mul_comm _ ((3 : ZMod (2 ^ q)) ^ L),
      G_three_pow_mul_inv, one_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hξ]
  refine ⟨h1, ?_⟩
  rw [kappaN, h1]
  have : (3 ^ L * (ξ : ℤ) - (3 ^ L * (ξ : ℤ) - 2 ^ q * κ)) = 2 ^ q * κ := by ring
  rw [this, Int.mul_ediv_cancel_left _ (by positivity)]

/-- Lemma 8.2 (i): if `n_b ≤ L`, then `θ_b(N) = ⟨κ(N) 2^{−d_b}⟩_{3^{n_b}}/3^{n_b}`. -/
theorem theta_kappa (q s L P : ℕ) (τ : Fin (s - P) → Bool) (k : ℕ) (N : ℤ) (hn : nb q s P τ k ≤ L) :
    theta q s P τ k N =
      (((kappaN q L N : ZMod (3 ^ nb q s P τ k)) *
          ((2 : ZMod (3 ^ nb q s P τ k)) ^ db s P k)⁻¹).val : ℝ) / 3 ^ nb q s P τ k := by
  have key : ((-N : ℤ) : ZMod (3 ^ nb q s P τ k)) * ((2 : ZMod (3 ^ nb q s P τ k)) ^ (db s P k + q))⁻¹ =
      (kappaN q L N : ZMod (3 ^ nb q s P τ k)) * ((2 : ZMod (3 ^ nb q s P τ k)) ^ db s P k)⁻¹ := by
    apply G_inv2_shift
    conv_lhs => rw [kappaN_spec q L N]
    push_cast
    rw [G_three_pow_zero _ _ hn]; ring
  simp only [theta, inv2mod, key]

/-- `m₁ = −(3^k+1)/2` (Lemma 8.2 (ii)). -/
def mOne (k : ℕ) : ℤ := -(((3 : ℤ) ^ k + 1) / 2)
/-- `m₂ = (3^{k−1}−1)/2` (Lemma 8.2 (ii)). -/
def mTwo (k : ℕ) : ℤ := ((3 : ℤ) ^ (k - 1) - 1) / 2

/-- `I_k(ξ)` (Lemma 8.2 (ii)): `{κ₀(ξ)}` for `k = 0`, and two intervals of length `3^{k−1}` for `k ≥ 1`. -/
noncomputable def Ik (q L k ξ : ℕ) : Finset ℤ :=
  if k = 0 then {kappa0 q L ξ}
  else Ico (kappa0 q L ξ + mOne k + 1) (kappa0 q L ξ + mOne k + 1 + 3 ^ (k - 1)) ∪
    Ico (kappa0 q L ξ + mTwo k + 1) (kappa0 q L ξ + mTwo k + 1 + 3 ^ (k - 1))

/-- `κ₀(ξ)` satisfies `2^q κ₀ ≤ 3^L ξ + 2^{q−1} < 2^q κ₀ + 2^q`. -/
theorem G_kappa0_bounds (q L ξ : ℕ) :
    (2 : ℤ) ^ q * kappa0 q L ξ ≤ 3 ^ L * (ξ : ℤ) + 2 ^ (q - 1) ∧
      3 ^ L * (ξ : ℤ) + 2 ^ (q - 1) < 2 ^ q * kappa0 q L ξ + 2 ^ q := by
  have h1 := Nat.mul_div_le (3 ^ L * ξ + 2 ^ (q - 1)) (2 ^ q)
  have h2 := cpt_lt_mul_div_self_add (x := 3 ^ L * ξ + 2 ^ (q - 1)) (show 0 < 2 ^ q by positivity)
  unfold kappa0
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- `3^k` is odd. -/
theorem G_three_pow_odd (k : ℕ) : (3 : ℤ) ^ k % 2 = 1 := by
  have : Odd ((3 : ℤ) ^ k) := Odd.pow (by decide)
  exact Int.odd_iff.mp this

/-- Lemma 8.2 (ii): `κ ∈ I_k(ξ)` if and only if `3^L ξ − 2^q κ ∈ J_k` (`q ≥ 1`). -/
theorem G_mem_Ik_iff (q L k ξ : ℕ) (hq : 1 ≤ q) (κ : ℤ) :
    κ ∈ Ik q L k ξ ↔ 3 ^ L * (ξ : ℤ) - 2 ^ q * κ ∈ shell q k := by
  obtain ⟨hk1, hk2⟩ := G_kappa0_bounds q L ξ
  set κ0 := kappa0 q L ξ
  set X := (3 : ℤ) ^ L * (ξ : ℤ)
  set h := (2 : ℤ) ^ (q - 1) with hh
  have hQ : (2 : ℤ) ^ q = 2 * h := by
    rw [hh, ← pow_succ']; congr 1; omega
  rw [hQ] at hk1 hk2 ⊢
  have hpos : 0 < h := by positivity
  -- characterization of the floor
  have F1 : ∀ y : ℤ, X + h < 2 * h * y ↔ κ0 + 1 ≤ y := by
    intro y; constructor
    · intro hy; by_contra hc; push Not at hc
      have : 2 * h * y ≤ 2 * h * κ0 := by
        apply mul_le_mul_of_nonneg_left (by omega) (by positivity)
      linarith
    · intro hy
      have : 2 * h * (κ0 + 1) ≤ 2 * h * y := mul_le_mul_of_nonneg_left hy (by positivity)
      linarith
  have F2 : ∀ y : ℤ, 2 * h * y ≤ X + h ↔ y ≤ κ0 := by
    intro y; constructor
    · intro hy; by_contra hc; push Not at hc
      have : 2 * h * (κ0 + 1) ≤ 2 * h * y := mul_le_mul_of_nonneg_left (by omega) (by positivity)
      linarith
    · intro hy
      have : 2 * h * y ≤ 2 * h * κ0 := mul_le_mul_of_nonneg_left hy (by positivity)
      linarith
  unfold Ik shell
  by_cases hk : k = 0
  · simp only [hk, ite_true, Finset.mem_singleton, Finset.mem_Ico]
    constructor
    · rintro rfl; constructor <;> linarith
    · rintro ⟨ha, hb⟩
      have e1 := (F2 κ).mp (by linarith)
      have e2 := (F1 (κ + 1)).mp (by linarith)
      omega
  · simp only [hk, ite_false, Finset.mem_union, Finset.mem_Ico]
    set U := (3 : ℤ) ^ (k - 1) with hU
    have h3k : (3 : ℤ) ^ k = 3 * U := by rw [hU, ← pow_succ']; congr 1; omega
    have hodd := G_three_pow_odd (k - 1)
    rw [← hU] at hodd
    have he1 : 2 * (((3 : ℤ) ^ k + 1) / 2) = 3 * U + 1 := by
      rw [h3k]; omega
    have he2 : 2 * (((3 : ℤ) ^ (k - 1) - 1) / 2) = U - 1 := by
      rw [← hU]; omega
    unfold mOne mTwo
    rw [← hU]
    set e1 := ((3 : ℤ) ^ k + 1) / 2
    set e2 := ((3 : ℤ) ^ (k - 1) - 1) / 2
    rw [h3k]
    have p1 : h * (2 * e1) = h * (3 * U + 1) := by rw [he1]
    have p2 : h * (2 * e2) = h * (U - 1) := by rw [he2]
    -- the positive half
    have Pos : (κ0 + -e1 + 1 ≤ κ ∧ κ < κ0 + -e1 + 1 + U) ↔
        (h * U ≤ X - 2 * h * κ ∧ X - 2 * h * κ < h * (3 * U)) := by
      constructor
      · rintro ⟨a1, a2⟩
        have b1 := (F2 (κ + e1 - U)).mpr (by linarith)
        have b2 := (F1 (κ + e1)).mpr (by linarith)
        constructor <;> nlinarith
      · rintro ⟨a1, a2⟩
        have b1 := (F2 (κ + e1 - U)).mp (by nlinarith)
        have b2 := (F1 (κ + e1)).mp (by nlinarith)
        constructor <;> linarith
    -- the negative half
    have Neg : (κ0 + e2 + 1 ≤ κ ∧ κ < κ0 + e2 + 1 + U) ↔
        (-(h * (3 * U)) ≤ X - 2 * h * κ ∧ X - 2 * h * κ < -(h * U)) := by
      constructor
      · rintro ⟨a1, a2⟩
        have b1 := (F2 (κ - e2 - U)).mpr (by linarith)
        have b2 := (F1 (κ - e2)).mpr (by linarith)
        constructor <;> nlinarith
      · rintro ⟨a1, a2⟩
        have b1 := (F2 (κ - e2 - U)).mp (by nlinarith)
        have b2 := (F1 (κ - e2)).mp (by nlinarith)
        constructor <;> linarith
    rw [Pos, Neg]

/-- Lemma 8.2 (ii)(iii): the sum over the shell `J_k` is the sum over `(ξ, κ)` (`ξ ∈ [0, 2^q)`, `κ ∈ I_k(ξ)`). -/
theorem shell_fiber (q L : ℕ) (hq : 1 ≤ q) (k : ℕ) (F : ℤ → ℝ) :
    ∑ N ∈ shell q k, F N = ∑ ξ ∈ range (2 ^ q), ∑ κ ∈ Ik q L k ξ, F (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij' (fun N => (⟨xiN q L N, kappaN q L N⟩ : Σ _ : ℕ, ℤ))
    (fun x => 3 ^ L * (x.1 : ℤ) - 2 ^ q * x.2)
  · intro N hN
    simp only [Finset.mem_sigma, Finset.mem_range] at hN ⊢
    refine ⟨ZMod.val_lt _, ?_⟩
    rw [G_mem_Ik_iff q L k _ hq, ← kappaN_spec]; exact hN
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    exact (G_mem_Ik_iff q L k _ hq _).mp hx.2
  · intro N _
    simp only
    exact (kappaN_spec q L N).symm
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨h1, h2⟩ := xiN_kappaN_of q L x.1 hx.1 x.2
    simp only [h1, h2]
  · intro N _
    simp only
    rw [← kappaN_spec]

/-- `#I_k(ξ) = #J_k / 2^q`: 1 for `k = 0`, and `2·3^{k−1}` for `k ≥ 1`. -/
theorem Ik_card (q L k ξ : ℕ) : (Ik q L k ξ).card = if k = 0 then 1 else 2 * 3 ^ (k - 1) := by
  unfold Ik
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    set U := (3 : ℤ) ^ (k - 1) with hU
    have hodd := G_three_pow_odd (k - 1)
    rw [← hU] at hodd
    have h3k : (3 : ℤ) ^ k = 3 * U := by rw [hU, ← pow_succ']; congr 1; omega
    have he1 : 2 * (((3 : ℤ) ^ k + 1) / 2) = 3 * U + 1 := by rw [h3k]; omega
    have he2 : 2 * (((3 : ℤ) ^ (k - 1) - 1) / 2) = U - 1 := by rw [← hU]; omega
    unfold mOne mTwo
    rw [← hU] at he2 ⊢
    set e1 := ((3 : ℤ) ^ k + 1) / 2
    set e2 := (U - 1) / 2
    have hdisj : Disjoint (Ico (kappa0 q L ξ + -e1 + 1) (kappa0 q L ξ + -e1 + 1 + U))
        (Ico (kappa0 q L ξ + e2 + 1) (kappa0 q L ξ + e2 + 1 + U)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Ico] at hx hx'
      omega
    rw [Finset.card_union_of_disjoint hdisj, Int.card_Ico, Int.card_Ico]
    have : ((3 : ℤ) ^ (k - 1)).toNat = 3 ^ (k - 1) := by
      rw [show ((3 : ℤ) ^ (k - 1)) = ((3 ^ (k - 1) : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]
    rw [show kappa0 q L ξ + -e1 + 1 + U - (kappa0 q L ξ + -e1 + 1) = U by ring,
      show kappa0 q L ξ + e2 + 1 + U - (kappa0 q L ξ + e2 + 1) = U by ring, hU, this]
    ring

/-- The points of the shell `J_k` satisfy `|N| ≤ 2^{q−1} max(1, 3^k)`. -/
theorem shell_abs (q k : ℕ) (N : ℤ) (hN : N ∈ shell q k) :
    |(N : ℝ)| ≤ 2 ^ (q - 1) * max 1 ((3:ℝ) ^ k) := by
  unfold shell at hN
  by_cases hk : k = 0
  · simp only [hk, ite_true, Finset.mem_Ico] at hN
    simp only [hk, pow_zero, max_self, mul_one]
    have h1 : (-(2 ^ (q - 1) : ℝ)) ≤ N := by exact_mod_cast hN.1
    have h2 : (N : ℝ) < 2 ^ (q - 1) := by exact_mod_cast hN.2
    rw [abs_le]; constructor <;> linarith
  · simp only [hk, ite_false, Finset.mem_union, Finset.mem_Ico] at hN
    have h1 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    rw [max_eq_right h1]
    have hle : (3 : ℝ) ^ (k - 1) ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have hp : (0 : ℝ) ≤ 2 ^ (q - 1) * 3 ^ (k - 1) := by positivity
    have hp' : (2 : ℝ) ^ (q - 1) * 3 ^ (k - 1) ≤ 2 ^ (q - 1) * 3 ^ k :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    rcases hN with ⟨a, b⟩ | ⟨a, b⟩
    · have a' : ((2 : ℝ) ^ (q - 1) * 3 ^ (k - 1)) ≤ N := by exact_mod_cast a
      have b' : (N : ℝ) < 2 ^ (q - 1) * 3 ^ k := by exact_mod_cast b
      rw [abs_le]; constructor <;> linarith
    · have a' : -((2 : ℝ) ^ (q - 1) * 3 ^ k) ≤ N := by exact_mod_cast a
      have b' : (N : ℝ) < -(2 ^ (q - 1) * 3 ^ (k - 1)) := by exact_mod_cast b
      rw [abs_le]; constructor <;> linarith

/-- `u = −3^{−n} mod 2^d` (Lemma 8.3). -/
noncomputable def ub (d n : ℕ) : ℕ := (-(((3 : ZMod (2 ^ d)) ^ n)⁻¹)).val

set_option linter.unusedVariables false in
/-- Lemma 8.3: if `1 ≤ n_b ≤ L` and `d_b ≥ 1`, then for some integer `m`
`θ_b(N) = (u_b κ + 3^{e_b} ξ/2^q)/2^{d_b} − N/(2^{q+d_b} 3^{n_b}) + m` (`ξ = ξ_N`, `κ = κ(N)`, `e_b = L − n_b`). -/
theorem theta_phase (q s L P : ℕ) (τ : Fin (s - P) → Bool) (k : ℕ) (N : ℤ)
    (hn1 : 1 ≤ nb q s P τ k) (hn : nb q s P τ k ≤ L) (hd : 1 ≤ db s P k) :
    ∃ m : ℤ, theta q s P τ k N =
      ((ub (db s P k) (nb q s P τ k) : ℝ) * (kappaN q L N : ℝ) +
          (3:ℝ) ^ (L - nb q s P τ k) * (xiN q L N : ℝ) / 2 ^ q) / 2 ^ db s P k -
        (N : ℝ) / (2 ^ (q + db s P k) * 3 ^ nb q s P τ k) + m := by
  -- the proof does not use `hn1` or `hd` (the formula also holds when `n_b = 0` or `d_b = 0`)
  rw [theta_kappa q s L P τ k N hn]
  set n := nb q s P τ k
  set d := db s P k
  set κ := kappaN q L N
  set ξ := xiN q L N
  set v := ((κ : ZMod (3 ^ n)) * ((2 : ZMod (3 ^ n)) ^ d)⁻¹).val with hv
  set u := ub d n with hu
  have hN := kappaN_spec q L N
  -- `v 2^d ≡ κ (mod 3^n)`
  obtain ⟨j, hj⟩ : ((3 ^ n : ℕ) : ℤ) ∣ κ - (v : ℤ) * 2 ^ d := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hv, ZMod.natCast_zmod_val, mul_assoc, mul_comm _ ((2 : ZMod (3 ^ n)) ^ d), G_two_pow_mul_inv,
      mul_one]
  -- `u 3^n ≡ −1 (mod 2^d)`
  obtain ⟨i, hi⟩ : ((2 ^ d : ℕ) : ℤ) ∣ (u : ℤ) * 3 ^ n - (-1) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hu, ub, ZMod.natCast_zmod_val, neg_mul, mul_comm, G_three_pow_mul_inv]
  refine ⟨-(i * j) - u * v, ?_⟩
  push_cast at hj hi ⊢
  have hjR : (κ : ℝ) - (v : ℝ) * 2 ^ d = 3 ^ n * j := by exact_mod_cast hj
  have hiR : (u : ℝ) * 3 ^ n + 1 = 2 ^ d * i := by
    have : ((u : ℤ) * 3 ^ n + 1 : ℤ) = 2 ^ d * i := by linarith
    exact_mod_cast this
  have hNR : (N : ℝ) = 3 ^ L * (ξ : ℝ) - 2 ^ q * κ := by exact_mod_cast hN
  have h3L : (3 : ℝ) ^ L = 3 ^ (L - n) * 3 ^ n := by rw [← pow_add]; congr 1; omega
  rw [hNR, h3L, pow_add]
  field_simp
  linear_combination (-((2:ℝ) ^ q * (1 + 3 ^ n * (u:ℝ)))) * hjR + (-((2:ℝ) ^ q * 3 ^ n * (j:ℝ))) * hiR

/-- Lemma 8.4: in the swap block `k`, `d_b = λ(L − n_b + 1) + H_b − h_L` (`H_b` is the height just before the block). -/
theorem dist_formula (q s L P : ℕ) (τ : Fin (s - P) → Bool) (k : ℕ) (hk : IsSwap q s P τ k) :
    (db s P k : ℝ) = lam * ((L : ℝ) - nb q s P τ k + 1) + hw (hp q P) τ (2 * k - 1) - hL s L := by
  obtain ⟨h2k, hk1, -, -⟩ := hk
  have hPs : P ≤ s := by omega
  have hdb : (db s P k : ℝ) = (s : ℝ) - P - (2 * (k : ℝ) - 1) := by
    unfold db
    rw [Nat.cast_sub (by omega), Nat.cast_sub hPs, Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hdb]
  unfold nb jb hw hp hL
  rw [Nat.cast_sub (by omega)]
  push_cast; ring

/-- Corollary of Lemma 8.4: in a swap block with `n_b ≤ L`, `3^{e_b}/2^{d_b} ≤ 2^{h_L − 1}/3`. -/
theorem dist_bound (q s L P : ℕ) (τ : Fin (s - P) → Bool) (k : ℕ) (hk : IsSwap q s P τ k)
    (hn : nb q s P τ k ≤ L) :
    (3:ℝ) ^ (L - nb q s P τ k) / 2 ^ db s P k ≤ (2:ℝ) ^ (hL s L - 1) / 3 := by
  have hf := dist_formula q s L P τ k hk
  obtain ⟨-, -, -, hH⟩ := hk
  set H := hw (hp q P) τ (2 * k - 1)
  have he : ((L - nb q s P τ k : ℕ) : ℝ) = (L : ℝ) - nb q s P τ k := by
    rw [Nat.cast_sub hn]
  have hl3 : (3 : ℝ) ^ (L - nb q s P τ k) = (2 : ℝ) ^ (lam * ((L - nb q s P τ k : ℕ) : ℝ)) := by
    rw [Real.rpow_mul (by norm_num), ← G_three_eq_rpow, Real.rpow_natCast]
  have hl2 : (2 : ℝ) ^ db s P k = (2 : ℝ) ^ ((db s P k : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  rw [hl3, hl2, ← Real.rpow_sub (by norm_num), G_three_eq_rpow, ← Real.rpow_sub (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [he, hf]; linarith

/-- Lemma 8.5 (injectivity): if the `d_i ≥ 2` are distinct and all of the same parity and the `u_i` are odd, then for
`σ, σ'` with coefficients in `{−1, 0, 1}`, `Σ (σ_i − σ'_i) u_i 2^{−d_i} ∈ ℤ` implies `σ = σ'`. -/
theorem sign_inj {m : ℕ} (d : Fin m → ℕ) (u : Fin m → ℤ) (hd2 : ∀ i, 2 ≤ d i)
    (hinj : Function.Injective d) (hpar : ∀ i j, d i % 2 = d j % 2) (hu : ∀ i, u i % 2 = 1)
    (σ σ' : Fin m → ℤ) (hσ : ∀ i, |σ i| ≤ 1) (hσ' : ∀ i, |σ' i| ≤ 1)
    (hz : ∃ z : ℤ, ∑ i, ((σ i - σ' i) * u i : ℝ) / 2 ^ d i = z) : σ = σ' := by
  have h := G_sign_core univ d u (fun i => σ i - σ' i) (fun i _ => hd2 i) (hinj.injOn)
    (fun i _ j _ => hpar i j) (fun i _ => hu i)
    (fun i _ => by
      have := abs_sub (σ i) (σ' i)
      linarith [hσ i, hσ' i])
    (by obtain ⟨z, hz⟩ := hz; exact ⟨z, by push_cast; exact hz⟩)
  funext i
  have := h i (Finset.mem_univ i)
  linarith

end Collatz.M1
