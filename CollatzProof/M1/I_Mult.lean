import CollatzProof.M1.I_Kernel
import CollatzProof.M1.DeepDefs

/-!
# Auxiliary results for §11.3: upper bound on the multiplicity `mult(v)` (Lemma 11.4, Proposition 11.5)

For `n = h + 2^D j` (`1 ≤ h < 2^D`, `0 ≤ j < 2^q`) and `M = 2^{q+D}`,
let `w(n) = I_kf(2^q‖n/M‖)` (`2^q‖n/M‖ = |n|_M/2^D`) and `K(v, n) = I_kf(2^q‖(n3^L/2^D − v)/2^q‖ − B)` (`= I_kf(d(v,n) − B)`);
under the lattice condition `λ₁(Λ_L) ≥ q2^D(B+1)` we show `Σ_{h,j} w(n)K(v, n) ≤ 25` (`I_mult_le`).

Proposition 11.5 of the manuscript obtains `200/9` by a double dyadic decomposition in `n` and in the distance. Here the weight of each `n` is bounded above by the weight
`(1/2)^k (1/2)^i` of a single class (`I_class_idx`), and the points in the cumulative boxes are counted by a packing argument (`I_lattice_count`).
For `q ≥ 2` the bound is `5 · 5 = 25`.
-/

namespace Collatz.M1

open Finset

/-- Class index: if `x < 2^m`, then for some `k ≤ m`, `x < 2^k` and `I_kf x ≤ (1/2)^k`. -/
lemma I_class_idx (x : ℝ) (m : ℕ) (hx : x < 2 ^ m) :
    ∃ k ∈ range (m + 1), x < 2 ^ k ∧ I_kf x ≤ (1 / 2) ^ k := by
  by_cases h1 : x < 1
  · exact ⟨0, by simp, by simpa using h1, by simpa using I_kf_le_one x⟩
  · push Not at h1
    have hx0 : 0 ≤ x := by linarith
    set f := ⌊x⌋₊ with hf
    have hf1 : 1 ≤ f := Nat.le_floor (by simpa using h1)
    have hpow_le : 2 ^ (Nat.log 2 f) ≤ f := Nat.pow_log_le_self 2 (by omega)
    have hlt_pow : f < 2 ^ (Nat.log 2 f + 1) := Nat.lt_pow_succ_log_self (by norm_num) f
    have hlow : (2 : ℝ) ^ (Nat.log 2 f) ≤ x := by
      calc (2 : ℝ) ^ (Nat.log 2 f) = ((2 ^ Nat.log 2 f : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (f : ℝ) := by exact_mod_cast hpow_le
        _ ≤ x := Nat.floor_le hx0
    have hup : x < 2 ^ (Nat.log 2 f + 1) := by
      have h1' : x < f + 1 := Nat.lt_floor_add_one x
      have h2' : (f : ℝ) + 1 ≤ 2 ^ (Nat.log 2 f + 1) := by
        have : f + 1 ≤ 2 ^ (Nat.log 2 f + 1) := hlt_pow
        exact_mod_cast this
      linarith
    have hkm : Nat.log 2 f + 1 ≤ m := by
      have : f < 2 ^ m := (Nat.floor_lt hx0).mpr (by exact_mod_cast hx)
      have := Nat.log_lt_of_lt_pow (by omega) this
      omega
    refine ⟨Nat.log 2 f + 1, mem_range.mpr (by omega), hup, ?_⟩
    have hxpos : 0 < x := by linarith
    calc I_kf x ≤ 1 / (2 * x) := I_kf_le_inv x hxpos
      _ ≤ 1 / (2 * 2 ^ (Nat.log 2 f)) := one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (1 / 2) ^ (Nat.log 2 f + 1) := by rw [one_div_pow, pow_succ']

/-- Packing (the form of Lemma 11.4): count the points of `Λ_L` by the first coordinate `b ≡ n` (`|b| = 2^D·2^q‖n/M‖`) and
the second coordinate `a ≡ 3^L n` (`|a − 2^D v| = 2^D·2^q‖y₀‖`). -/
lemma I_lattice_count (q D L : ℕ) (B : ℝ) (hB : 0 ≤ B) (hq : 1 ≤ q) (v : ℤ) (k i : ℕ)
    (hlat : LatticeCond q L D (q * 2 ^ D * (B + 1))) :
    (((Ico 1 (2 ^ D) ×ˢ range (2 ^ q)).filter (fun hj : ℕ × ℕ =>
        2 ^ q * I_nd (((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) / 2 ^ (q + D)) < 2 ^ k ∧
        2 ^ q * I_nd ((((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q) - B < 2 ^ i)).card
        : ℝ) ≤
      (1 + 2 ^ (D + k + 1) / (q * 2 ^ D * (B + 1))) *
        (1 + 2 ^ (D + 1) * (B + 2 ^ i) / (q * 2 ^ D * (B + 1))) := by
  set lam1 : ℝ := q * 2 ^ D * (B + 1) with hlam1
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlam : 0 < lam1 := by rw [hlam1]; positivity
  set M : ℕ := 2 ^ (q + D) with hM
  have hMr : ((M : ℕ) : ℝ) = 2 ^ q * 2 ^ D := by rw [hM]; push_cast; ring
  have hMz : ((M : ℕ) : ℤ) = 2 ^ (q + D) := by rw [hM]; push_cast; ring
  -- the lattice points
  let nn : ℕ × ℕ → ℕ := fun hj => hj.1 + 2 ^ D * hj.2
  let rb : ℕ × ℕ → ℤ := fun hj => round (((nn hj : ℕ) : ℝ) / 2 ^ (q + D))
  let ra : ℕ × ℕ → ℤ := fun hj => round ((((nn hj : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q)
  let bf : ℕ × ℕ → ℤ := fun hj => (nn hj : ℤ) - 2 ^ (q + D) * rb hj
  let af : ℕ × ℕ → ℤ := fun hj => 3 ^ L * (nn hj : ℤ) - 2 ^ (q + D) * ra hj
  have hb_abs : ∀ hj, |((bf hj : ℤ) : ℝ)| =
      2 ^ D * (2 ^ q * I_nd (((nn hj : ℕ) : ℝ) / 2 ^ (q + D))) := by
    intro hj
    have e : ((bf hj : ℤ) : ℝ) = 2 ^ (q + D) * (((nn hj : ℕ) : ℝ) / 2 ^ (q + D) - (rb hj : ℝ)) := by
      simp only [bf]; push_cast; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity), I_nd]
    simp only [rb]
    rw [pow_add]; ring
  have ha_abs : ∀ hj, |((af hj : ℤ) : ℝ) - 2 ^ D * v| =
      2 ^ D * (2 ^ q * I_nd ((((nn hj : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q)) := by
    intro hj
    have e : ((af hj : ℤ) : ℝ) - 2 ^ D * v =
        2 ^ (q + D) * ((((nn hj : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q - (ra hj : ℝ)) := by
      simp only [af]; push_cast; rw [pow_add]; field_simp; ring
    rw [e, abs_mul, abs_of_pos (by positivity), I_nd]
    simp only [ra]
    rw [pow_add]; ring
  have hcong : ∀ hj, (2 : ℤ) ^ (q + D) ∣ af hj - 3 ^ L * bf hj := by
    intro hj
    exact ⟨3 ^ L * rb hj - ra hj, by simp only [af, bf]; ring⟩
  -- the map to cells
  set T := (Ico 1 (2 ^ D) ×ˢ range (2 ^ q)).filter (fun hj : ℕ × ℕ =>
        2 ^ q * I_nd (((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) / 2 ^ (q + D)) < 2 ^ k ∧
        2 ^ q * I_nd ((((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q) - B < 2 ^ i)
    with hT
  set K1 : ℤ := ⌊(2 : ℝ) ^ (D + k + 1) / lam1⌋ with hK1
  set K2 : ℤ := ⌊(2 : ℝ) ^ (D + 1) * (B + 2 ^ i) / lam1⌋ with hK2
  let φ : ℕ × ℕ → ℤ × ℤ := fun hj =>
    (⌊(((bf hj : ℤ) : ℝ) + 2 ^ (D + k)) / lam1⌋,
      ⌊(((af hj : ℤ) : ℝ) - 2 ^ D * v + 2 ^ D * (B + 2 ^ i)) / lam1⌋)
  have hmaps : Set.MapsTo φ (T : Set (ℕ × ℕ)) ((Icc 0 K1 ×ˢ Icc 0 K2 : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro hj hmem
    rw [coe_filter] at hmem
    obtain ⟨_, h1, h2⟩ := hmem
    have hb := hb_abs hj
    have ha := ha_abs hj
    have hbl : |((bf hj : ℤ) : ℝ)| < 2 ^ (D + k) := by
      rw [hb, show (2 : ℝ) ^ (D + k) = 2 ^ D * 2 ^ k from pow_add 2 D k]
      exact mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < 2 ^ D)
    have hal : |((af hj : ℤ) : ℝ) - 2 ^ D * v| < 2 ^ D * (B + 2 ^ i) := by
      rw [ha]; exact mul_lt_mul_of_pos_left (by linarith) (by positivity : (0 : ℝ) < 2 ^ D)
    rw [abs_lt] at hbl hal
    simp only [coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc, φ]
    refine ⟨⟨Int.floor_nonneg.mpr (div_nonneg (by linarith) hlam.le), Int.floor_mono ?_⟩,
      ⟨Int.floor_nonneg.mpr (div_nonneg (by nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) D])
        hlam.le), Int.floor_mono ?_⟩⟩
    · apply div_le_div_of_nonneg_right _ hlam.le
      rw [pow_succ]; linarith
    · apply div_le_div_of_nonneg_right _ hlam.le
      rw [pow_succ]; nlinarith
  have hinj : Set.InjOn φ (T : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    rw [coe_filter] at hx hy
    have hx1 := (mem_product.mp hx.1)
    have hy1 := (mem_product.mp hy.1)
    simp only [Prod.mk.injEq, φ] at hxy
    obtain ⟨e1, e2⟩ := hxy
    have d1 := Int.abs_sub_lt_one_of_floor_eq_floor e1
    have d2 := Int.abs_sub_lt_one_of_floor_eq_floor e2
    rw [← sub_div, abs_div, abs_of_pos hlam, div_lt_one hlam] at d1 d2
    have db : |((bf x - bf y : ℤ) : ℝ)| < lam1 := by push_cast; convert d1 using 2; ring
    have da : |((af x - af y : ℤ) : ℝ)| < lam1 := by push_cast; convert d2 using 2; ring
    have hbeq : bf x = bf y ∧ af x = af y := by
      by_contra hne
      have hne' : (af x - af y, bf x - bf y) ≠ ((0 : ℤ), (0 : ℤ)) := by
        intro h
        simp only [Prod.mk.injEq, sub_eq_zero] at h
        exact hne ⟨h.2, h.1⟩
      have hc : af x - af y ≡ 3 ^ L * (bf x - bf y) [ZMOD 2 ^ (q + D)] := by
        rw [Int.modEq_iff_dvd]
        have := dvd_sub (hcong y) (hcong x)
        rw [show 3 ^ L * (bf x - bf y) - (af x - af y) = af y - 3 ^ L * bf y - (af x - 3 ^ L * bf x) by
          ring]
        exact this
      have := hlat (af x - af y) (bf x - bf y) hne' hc
      rw [Int.cast_max, Int.cast_abs, Int.cast_abs] at this
      have := lt_of_le_of_lt this (max_lt da db)
      exact lt_irrefl _ this
    -- if the `b` are equal, then the `n` are equal
    have hn : (2 : ℤ) ^ (q + D) ∣ (nn y : ℤ) - (nn x : ℤ) := by
      have h := hbeq.1
      simp only [bf] at h
      exact ⟨rb y - rb x, by linarith⟩
    have hnx : nn x < 2 ^ (q + D) := by
      simp only [nn]
      have := hx1.1; have := hx1.2
      rw [mem_Ico] at *; rw [mem_range] at *
      calc x.1 + 2 ^ D * x.2 < 2 ^ D + 2 ^ D * x.2 := by omega
        _ = 2 ^ D * (x.2 + 1) := by ring
        _ ≤ 2 ^ D * 2 ^ q := Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ (q + D) := by ring
    have hny : nn y < 2 ^ (q + D) := by
      simp only [nn]
      have := hy1.1; have := hy1.2
      rw [mem_Ico] at *; rw [mem_range] at *
      calc y.1 + 2 ^ D * y.2 < 2 ^ D + 2 ^ D * y.2 := by omega
        _ = 2 ^ D * (y.2 + 1) := by ring
        _ ≤ 2 ^ D * 2 ^ q := Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ (q + D) := by ring
    have hmod : nn x ≡ nn y [MOD 2 ^ (q + D)] := by
      rw [Nat.modEq_iff_dvd]; push_cast; exact hn
    rw [Nat.ModEq, Nat.mod_eq_of_lt hnx, Nat.mod_eq_of_lt hny] at hmod
    simp only [nn] at hmod
    have hx1' := mem_Ico.mp hx1.1
    have hy1' := mem_Ico.mp hy1.1
    have e1 : (x.1 + 2 ^ D * x.2) % 2 ^ D = x.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx1'.2]
    have e2 : (y.1 + 2 ^ D * y.2) % 2 ^ D = y.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy1'.2]
    have e3 : (x.1 + 2 ^ D * x.2) / 2 ^ D = x.2 := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx1'.2, zero_add]
    have e4 : (y.1 + 2 ^ D * y.2) / 2 ^ D = y.2 := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy1'.2, zero_add]
    apply Prod.ext
    · rw [← e1, ← e2, hmod]
    · rw [← e3, ← e4, hmod]
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [card_product, Int.card_Icc, Int.card_Icc] at hcard
  have hK1n : 0 ≤ K1 := Int.floor_nonneg.mpr (by positivity)
  have hK2n : 0 ≤ K2 := Int.floor_nonneg.mpr (by positivity)
  have c1 : (((K1 + 1 - 0).toNat : ℕ) : ℝ) ≤ 1 + 2 ^ (D + k + 1) / lam1 := by
    have : (((K1 + 1 - 0).toNat : ℕ) : ℤ) = K1 + 1 := by rw [sub_zero]; exact Int.toNat_of_nonneg (by omega)
    have h' : (((K1 + 1 - 0).toNat : ℕ) : ℝ) = (K1 : ℝ) + 1 := by exact_mod_cast this
    rw [h']; have := Int.floor_le ((2 : ℝ) ^ (D + k + 1) / lam1); rw [← hK1] at this; linarith
  have c2 : (((K2 + 1 - 0).toNat : ℕ) : ℝ) ≤ 1 + 2 ^ (D + 1) * (B + 2 ^ i) / lam1 := by
    have : (((K2 + 1 - 0).toNat : ℕ) : ℤ) = K2 + 1 := by rw [sub_zero]; exact Int.toNat_of_nonneg (by omega)
    have h' : (((K2 + 1 - 0).toNat : ℕ) : ℝ) = (K2 : ℝ) + 1 := by exact_mod_cast this
    rw [h']; have := Int.floor_le ((2 : ℝ) ^ (D + 1) * (B + 2 ^ i) / lam1); rw [← hK2] at this; linarith
  calc (T.card : ℝ) ≤ (((K1 + 1 - 0).toNat * (K2 + 1 - 0).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (((K1 + 1 - 0).toNat : ℕ) : ℝ) * (((K2 + 1 - 0).toNat : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul c1 c2 (by positivity) (by positivity)

/-- The form of Proposition 11.5: if `q ≥ 2`, `B ≥ 0` and `λ₁(Λ_L) ≥ q2^D(B+1)`, then `Σ_{h,j} w(n)K(v, n) ≤ 25`. -/
lemma I_mult_le (q D L : ℕ) (B : ℝ) (hB : 0 ≤ B) (hq : 2 ≤ q) (v : ℤ)
    (hlat : LatticeCond q L D (q * 2 ^ D * (B + 1))) :
    ∑ h ∈ Ico 1 (2 ^ D), ∑ j ∈ range (2 ^ q),
      I_kf (2 ^ q * I_nd (((h + 2 ^ D * j : ℕ) : ℝ) / 2 ^ (q + D))) *
      I_kf (2 ^ q * I_nd ((((h + 2 ^ D * j : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q) - B) ≤ 25 := by
  set lam1 : ℝ := q * 2 ^ D * (B + 1) with hlam1
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlam : 0 < lam1 := by rw [hlam1]; positivity
  set S := Ico 1 (2 ^ D) ×ˢ range (2 ^ q) with hS
  let x1 : ℕ × ℕ → ℝ := fun hj => 2 ^ q * I_nd (((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) / 2 ^ (q + D))
  let x2 : ℕ × ℕ → ℝ := fun hj =>
    2 ^ q * I_nd ((((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q) - B
  let c : ℕ → ℝ := fun k => (1 / 2) ^ k
  have hc0 : ∀ k, 0 ≤ c k := fun k => by positivity
  -- turn the left-hand side into a sum over a product set
  rw [← sum_product' (f := fun h j => I_kf (2 ^ q * I_nd (((h + 2 ^ D * j : ℕ) : ℝ) / 2 ^ (q + D))) *
      I_kf (2 ^ q * I_nd ((((h + 2 ^ D * j : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q) - B))]
  -- bound for each point
  have hx1 : ∀ hj, x1 hj < 2 ^ q := by
    intro hj
    have := I_nd_le_half (((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) / 2 ^ (q + D))
    have h2 : (0 : ℝ) < 2 ^ q := by positivity
    simp only [x1]; nlinarith
  have hx2 : ∀ hj, x2 hj < 2 ^ q := by
    intro hj
    have := I_nd_le_half ((((hj.1 + 2 ^ D * hj.2 : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q)
    have h2 : (0 : ℝ) < 2 ^ q := by positivity
    simp only [x2]; nlinarith
  have hpt : ∀ hj ∈ S, I_kf (x1 hj) * I_kf (x2 hj) ≤
      ∑ k ∈ range (q + 1), ∑ i ∈ range (q + 1),
        c k * c i * (if x1 hj < 2 ^ k ∧ x2 hj < 2 ^ i then 1 else 0) := by
    intro hj _
    obtain ⟨k0, hk0, hk1, hk2⟩ := I_class_idx (x1 hj) q (hx1 hj)
    obtain ⟨i0, hi0, hi1, hi2⟩ := I_class_idx (x2 hj) q (hx2 hj)
    have hterm : I_kf (x1 hj) * I_kf (x2 hj) ≤
        c k0 * c i0 * (if x1 hj < 2 ^ k0 ∧ x2 hj < 2 ^ i0 then 1 else 0) := by
      rw [if_pos ⟨hk1, hi1⟩, mul_one]
      exact mul_le_mul hk2 hi2 (I_kf_nonneg _) (hc0 _)
    refine le_trans hterm ?_
    have hnn : ∀ k i, 0 ≤ c k * c i * (if x1 hj < 2 ^ k ∧ x2 hj < 2 ^ i then (1 : ℝ) else 0) := by
      intro k i; apply mul_nonneg (mul_nonneg (hc0 _) (hc0 _)); split_ifs <;> norm_num
    refine le_trans ?_ (single_le_sum (fun k _ => sum_nonneg fun i _ => hnn k i) hk0)
    exact single_le_sum (fun i _ => hnn k0 i) hi0
  refine le_trans (sum_le_sum hpt) ?_
  have hswap : ∑ hj ∈ S, ∑ k ∈ range (q + 1), ∑ i ∈ range (q + 1),
      c k * c i * (if x1 hj < 2 ^ k ∧ x2 hj < 2 ^ i then (1 : ℝ) else 0) =
      ∑ k ∈ range (q + 1), ∑ i ∈ range (q + 1), c k * c i *
        ∑ hj ∈ S, (if x1 hj < 2 ^ k ∧ x2 hj < 2 ^ i then (1 : ℝ) else 0) := by
    rw [sum_comm]; apply sum_congr rfl; intro k _; rw [sum_comm]; apply sum_congr rfl; intro i _
    rw [mul_sum]
  rw [hswap]
  -- number of points in each class
  have hcnt : ∀ k i, ∑ hj ∈ S, (if x1 hj < 2 ^ k ∧ x2 hj < 2 ^ i then (1 : ℝ) else 0) ≤
      (1 + 2 ^ (D + k + 1) / lam1) * (1 + 2 ^ (D + 1) * (B + 2 ^ i) / lam1) := by
    intro k i
    rw [sum_boole]
    exact I_lattice_count q D L B hB (by omega) v k i hlat
  have hstep : ∑ k ∈ range (q + 1), ∑ i ∈ range (q + 1), c k * c i *
      ∑ hj ∈ S, (if x1 hj < 2 ^ k ∧ x2 hj < 2 ^ i then (1 : ℝ) else 0) ≤
      ∑ k ∈ range (q + 1), ∑ i ∈ range (q + 1), c k * c i *
        ((1 + 2 ^ (D + k + 1) / lam1) * (1 + 2 ^ (D + 1) * (B + 2 ^ i) / lam1)) := by
    apply sum_le_sum; intro k _; apply sum_le_sum; intro i _
    exact mul_le_mul_of_nonneg_left (hcnt k i) (mul_nonneg (hc0 _) (hc0 _))
  refine le_trans hstep ?_
  have hfac : ∑ k ∈ range (q + 1), ∑ i ∈ range (q + 1), c k * c i *
        ((1 + 2 ^ (D + k + 1) / lam1) * (1 + 2 ^ (D + 1) * (B + 2 ^ i) / lam1)) =
      (∑ k ∈ range (q + 1), c k * (1 + 2 ^ (D + k + 1) / lam1)) *
        (∑ i ∈ range (q + 1), c i * (1 + 2 ^ (D + 1) * (B + 2 ^ i) / lam1)) := by
    rw [sum_mul_sum]; apply sum_congr rfl; intro k _; apply sum_congr rfl; intro i _; ring
  rw [hfac]
  have hgeo : ∑ k ∈ range (q + 1), c k ≤ 2 := sum_geometric_two_le (q + 1)
  have hck : ∀ k : ℕ, c k * 2 ^ k = 1 := by
    intro k; simp only [c]; rw [← mul_pow]; norm_num
  have hF1 : ∑ k ∈ range (q + 1), c k * (1 + 2 ^ (D + k + 1) / lam1) ≤ 5 := by
    have e : ∑ k ∈ range (q + 1), c k * (1 + 2 ^ (D + k + 1) / lam1) =
        ∑ k ∈ range (q + 1), c k + (q + 1) * (2 ^ (D + 1) / lam1) := by
      have : ∀ k ∈ range (q + 1), c k * (1 + 2 ^ (D + k + 1) / lam1) = c k + 2 ^ (D + 1) / lam1 := by
        intro k _
        rw [mul_add, mul_one, show (2 : ℝ) ^ (D + k + 1) = 2 ^ k * 2 ^ (D + 1) by ring,
          mul_div_assoc, ← mul_assoc, hck, one_mul]
      rw [sum_congr rfl this, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    rw [e]
    have : (q + 1 : ℝ) * (2 ^ (D + 1) / lam1) ≤ 3 := by
      rw [hlam1, pow_succ, mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      have h2D : (0 : ℝ) < 2 ^ D := by positivity
      nlinarith [mul_nonneg h2D.le hB, mul_nonneg (mul_nonneg h2D.le hB) (by linarith : (0 : ℝ) ≤ q - 2)]
    linarith
  have hF2 : ∑ i ∈ range (q + 1), c i * (1 + 2 ^ (D + 1) * (B + 2 ^ i) / lam1) ≤ 5 := by
    have : ∀ i ∈ range (q + 1), c i * (1 + 2 ^ (D + 1) * (B + 2 ^ i) / lam1) =
        c i + (2 ^ (D + 1) / lam1) * (B * c i + 1) := by
      intro i _
      have := hck i
      field_simp
      rw [show c i * (lam1 + 2 ^ (D + 1) * (B + 2 ^ i)) =
        c i * lam1 + 2 ^ (D + 1) * B * c i + 2 ^ (D + 1) * (c i * 2 ^ i) by ring, this]
      ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, sum_const,
      card_range, nsmul_eq_mul]
    have hpos : 0 ≤ 2 ^ (D + 1) / lam1 := by positivity
    have h1 : (2 : ℝ) ^ (D + 1) / lam1 * (B * ∑ i ∈ range (q + 1), c i + (q + 1 : ℕ) * 1) ≤
        2 ^ (D + 1) / lam1 * (2 * B + q + 1) := by
      apply mul_le_mul_of_nonneg_left _ hpos
      push_cast; nlinarith
    have h2 : (2 : ℝ) ^ (D + 1) / lam1 * (2 * B + q + 1) ≤ 3 := by
      rw [hlam1, pow_succ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h2D : (0 : ℝ) < 2 ^ D := by positivity
      nlinarith [mul_nonneg h2D.le hB, mul_nonneg (mul_nonneg h2D.le hB) (by linarith : (0 : ℝ) ≤ q - 2)]
    linarith
  have hF1n : 0 ≤ ∑ k ∈ range (q + 1), c k * (1 + 2 ^ (D + k + 1) / lam1) :=
    sum_nonneg fun k _ => mul_nonneg (hc0 _) (by positivity)
  nlinarith

end Collatz.M1
