import CollatzProof.M1.S9
import CollatzProof.M1.S10

/-!
# Auxiliary results for §14: analytic lemmas and properties of the constants

Estimates independent of the individual components, used in assembling Proposition 14.1 (`all_shells` in `S14.lean`).
- Eventually valid inequalities: polynomial × geometric sequence (`K_ev_small`), linear (`K_ev_lin`), logarithmic (`K_ev_log`).
- `Θ_γ(ρ) ≥ 3/4`, `Θ^{⌊(D−1)/2⌋} ≤ 2(Θ^{c_D/2})^q`, `err_k ≤ 2πq3^{k+1}2^{−q}`, `3^{k₁} ≤ 9·2^{δ'q+5+2Y}`.
- `1/2 ≤ φ_p ≤ 1 − 1/(2p)` (`p ≥ 2`; a weaker version of `1 − φ_p ≥ 1/p` (`p ≥ 80`) from Lemma 14.0 (a) of the manuscript, valid for all `p ≥ 2`).
- Simplifying the `1/p`-th power of the bound on `S_p^*(B)` (Proposition 11.3 etc.) (`K_root_bound`), and checking that the rates are `< 1` (`K_rate2`, `K_rate3`).
- If `W = 0`, then `A_k = 0` (`K_Ak_zero`; Proposition 10.2 assumes `W > 0`, so this case is treated separately).
-/

namespace Collatz.M1

open Finset Filter Topology

/-- A polynomial times a geometric sequence is eventually at most 1. -/
lemma K_ev_small (C : ℝ) (N : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∀ᶠ q : ℕ in atTop, C * ((q:ℝ) + 2) ^ N * u ^ q ≤ 1 := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one N
    (show |u| < 1 by rwa [abs_of_nonneg hu0])
  have ht2 : Tendsto (fun n : ℕ => (|C| + 1) * 3 ^ N * ((n:ℝ) ^ N * u ^ n)) atTop (𝓝 0) := by
    simpa using ht.const_mul ((|C| + 1) * 3 ^ N)
  have hev := ht2.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hev, eventually_ge_atTop 1] with q hq hq1
  have hq1' : (1:ℝ) ≤ q := by exact_mod_cast hq1
  have hu : 0 ≤ u ^ q := pow_nonneg hu0 q
  have h1 : ((q:ℝ) + 2) ^ N ≤ 3 ^ N * (q:ℝ) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) N
  have h2 : C * ((q:ℝ) + 2) ^ N * u ^ q ≤ (|C| + 1) * 3 ^ N * ((q:ℝ) ^ N * u ^ q) := by
    have hX : 0 ≤ ((q:ℝ) + 2) ^ N := by positivity
    calc C * ((q:ℝ) + 2) ^ N * u ^ q ≤ (|C| + 1) * ((q:ℝ) + 2) ^ N * u ^ q := by
          gcongr; linarith [le_abs_self C]
      _ ≤ (|C| + 1) * (3 ^ N * (q:ℝ) ^ N) * u ^ q := by gcongr
      _ = _ := by ring
  exact h2.trans hq

/-- Linear comparison: eventually `A ≤ c q`. -/
lemma K_ev_lin (A c : ℝ) (hc : 0 < c) : ∀ᶠ q : ℕ in atTop, A ≤ c * q := by
  filter_upwards [eventually_ge_atTop ⌈A / c⌉₊] with q hq
  have : A / c ≤ q := (Nat.le_ceil _).trans (by exact_mod_cast hq)
  rw [div_le_iff₀ hc] at this; linarith

/-- The logarithm is slower than linear: eventually `A + B log₂ q ≤ c q`. -/
lemma K_ev_log (A B c : ℝ) (hc : 0 < c) :
    ∀ᶠ q : ℕ in atTop, A + B * Real.logb 2 q ≤ c * q := by
  have hlo := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hε : 0 < c * Real.log 2 / (2 * (|B| + 1)) := by positivity
  have hb := hlo.bound hε
  filter_upwards [hb, K_ev_lin (2 * |A|) c hc, eventually_ge_atTop 1] with q hq hqA hq1
  simp only [Function.comp_apply, Real.norm_eq_abs, id] at hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  rw [abs_of_nonneg hq0] at hq
  have hlog : B * Real.logb 2 q ≤ c * q / 2 := by
    rw [Real.logb]
    have h1 : B * (Real.log q / Real.log 2) ≤ |B| * |Real.log q| / Real.log 2 := by
      rw [mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hl2.le
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |B| * |Real.log q| ≤ |B| * (c * Real.log 2 / (2 * (|B| + 1)) * q) :=
      mul_le_mul_of_nonneg_left hq (abs_nonneg B)
    have h3 : |B| * (c * Real.log 2 / (2 * (|B| + 1)) * q) ≤ c * Real.log 2 * q / 2 := by
      have hB : 0 ≤ |B| := abs_nonneg B
      rw [show |B| * (c * Real.log 2 / (2 * (|B| + 1)) * q) =
        (|B| / (|B| + 1)) * (c * Real.log 2 * q / 2) by field_simp]
      have : |B| / (|B| + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have : 0 ≤ c * Real.log 2 * q / 2 := by positivity
      nlinarith
    calc B * (Real.log q / Real.log 2) ≤ |B| * |Real.log q| / Real.log 2 := h1
      _ ≤ c * Real.log 2 * q / 2 / Real.log 2 := by
          apply div_le_div_of_nonneg_right (h2.trans h3) hl2.le
      _ = c * q / 2 := by field_simp
  linarith [le_abs_self A]

/-- `Θ_γ(ρ) ≥ 3/4` (`γ ∈ [1/2, 1]`). -/
lemma K_theta_ge (γ ρ : ℝ) (hγ : 1/2 ≤ γ) (hγ1 : γ ≤ 1) : 3/4 ≤ Theta γ ρ := by
  unfold Theta
  nlinarith [mul_nonneg (sub_nonneg.2 hγ1) (sq_nonneg (ρ - 1/2))]

/-- `Θ^{⌊(D−1)/2⌋} ≤ 2(Θ^{c_D/2})^q` (`D = ⌊c_D q⌋`, `3/4 ≤ Θ ≤ 1`). -/
lemma K_pow_floor (Θ cD : ℝ) (hΘ : 3/4 ≤ Θ) (hΘ1 : Θ ≤ 1) (q : ℕ) :
    Θ ^ ((⌊cD * q⌋₊ - 1) / 2) ≤ 2 * (Θ ^ (cD / 2)) ^ q := by
  have hΘ0 : 0 < Θ := by linarith
  set D := ⌊cD * q⌋₊ with hD
  have hDlt : cD * q < D + 1 := Nat.lt_floor_add_one _
  have h2m : D ≤ 2 * ((D - 1) / 2) + 2 := by omega
  have h2m' : (D:ℝ) ≤ 2 * (((D - 1) / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast h2m
  have hm : (cD * q - 4) / 2 ≤ (((D - 1) / 2 : ℕ) : ℝ) := by linarith
  rw [← Real.rpow_natCast]
  calc Θ ^ ((((D - 1) / 2 : ℕ) : ℝ)) ≤ Θ ^ ((cD * q - 4) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hΘ0 hΘ1 hm
    _ = (Θ ^ (cD / 2)) ^ q * Θ ^ (-2:ℝ) := by
        rw [← Real.rpow_mul_natCast hΘ0.le, ← Real.rpow_add hΘ0]; ring_nf
    _ ≤ (Θ ^ (cD / 2)) ^ q * 2 := by
        gcongr
        rw [Real.rpow_neg hΘ0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        nlinarith
    _ = 2 * (Θ ^ (cD / 2)) ^ q := by ring

/-- `err_k ≤ 2πq 3^{k+1} 2^{−q}`. -/
lemma K_errK_le (q k : ℕ) : errK q k ≤ 2 * Real.pi * q * 3 ^ (k + 1) * (1/2) ^ q := by
  have hpq : (0:ℝ) ≤ 2 * Real.pi * q := by positivity
  unfold errK
  split_ifs with hk
  · subst hk
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    have : (0:ℝ) ≤ ((2:ℝ) ^ q)⁻¹ := by positivity
    nlinarith
  · rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    obtain ⟨-, hL⟩ := Lp_spec q
    have hL' : ((2:ℝ) ^ q) < 3 * 3 ^ Lp q := by
      have : ((2 ^ q : ℕ) : ℝ) < ((3 ^ (Lp q + 1) : ℕ) : ℝ) := by exact_mod_cast hL
      push_cast at this; rw [pow_succ] at this; linarith
    have h3 : (0:ℝ) < 3 ^ Lp q := by positivity
    have h2 : (0:ℝ) < 2 ^ q := by positivity
    rw [mul_div_assoc', div_le_iff₀ h3, one_div, inv_pow, pow_succ]
    have : (0:ℝ) ≤ 3 ^ k := by positivity
    rw [show 2 * Real.pi * q * (3 ^ k * 3) * (2 ^ q)⁻¹ * 3 ^ Lp q =
      2 * Real.pi * q * 3 ^ k * ((3 * 3 ^ Lp q) / 2 ^ q) by field_simp]
    have hF : (1:ℝ) ≤ (3 * 3 ^ Lp q) / 2 ^ q := by rw [one_le_div h2]; linarith
    have hG : 0 ≤ 2 * Real.pi * q * 3 ^ k := by positivity
    exact le_mul_of_one_le_right hG hF

/-- `3^{y/λ} = 2^y`. -/
lemma K_three_rpow (y : ℝ) : (3:ℝ) ^ (y / lam) = 2 ^ y := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num), lam, Real.logb]
  congr 1
  field_simp

/-- `3^{k₁} ≤ 9·2^{δ'q+5+2Y}`. -/
lemma K_k1out_le (δ' Θs : ℝ) (s q : ℕ) (hY : 0 ≤ δ' * q + 5 + 2 * Yout δ' Θs s q) :
    (3:ℝ) ^ (k1out δ' Θs s q) ≤ 9 * (2:ℝ) ^ (δ' * q + 5 + 2 * Yout δ' Θs s q) := by
  set X := δ' * q + 5 + 2 * Yout δ' Θs s q with hX
  have hlam : 0 < lam := by have := lam_bounds; linarith
  have hx : 0 ≤ X / lam := div_nonneg hY hlam.le
  unfold k1out
  rw [← hX, pow_add, pow_one]
  have hc := Nat.ceil_lt_add_one hx
  have : (3:ℝ) ^ ⌈X / lam⌉₊ ≤ 3 ^ (X / lam + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hc.le
  rw [Real.rpow_add (by norm_num), Real.rpow_one, K_three_rpow] at this
  linarith


/-- `1/2 ≤ φ_p ≤ 1 − 1/(2p)` (`p ≥ 2` an integer). -/
lemma K_phiP (p : ℕ) (hp : 2 ≤ p) : 1/2 ≤ phiP p ∧ phiP p ≤ 1 - 1 / (2 * p) := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  set x : ℝ := 1 / ((p:ℝ) - 1) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hp1]; linarith
  have hr : (p:ℝ) / ((p:ℝ) - 1) = 1 + x := by rw [hx]; field_simp; ring
  unfold phiP
  rw [hr]
  set y : ℝ := (2:ℝ) ^ (-(1 + x)) + (2:ℝ) ^ (1 - 2 * (1 + x)) with hy
  have ha : (0:ℝ) < (2:ℝ) ^ (-(1 + x)) := by positivity
  have hb : (0:ℝ) < (2:ℝ) ^ (1 - 2 * (1 + x)) := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hinv0 : 0 ≤ 1 / (1 + x) := by positivity
  constructor
  · -- lower bound
    have h1 : ((2:ℝ) ^ (-(1 + x))) ^ (1 / (1 + x)) ≤ y ^ (1 / (1 + x)) :=
      Real.rpow_le_rpow ha.le (by linarith) hinv0
    rw [← Real.rpow_mul (by norm_num), show -(1 + x) * (1 / (1 + x)) = -1 by field_simp,
      Real.rpow_neg_one] at h1
    linarith
  · -- upper bound
    -- 2^{−x} ≤ 1 − x/2
    have hbern : (2:ℝ) ^ (-x) ≤ 1 - x / 2 := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num),
        show (2:ℝ)⁻¹ = 1 + (-1/2) by norm_num]
      have := _root_.rpow_one_add_le_one_add_mul_self (s := -1/2) (by norm_num) hx0.le hx1
      linarith
    have hyle : y ≤ 1 - x / 2 := by
      have e1 : (2:ℝ) ^ (-(1 + x)) = (1/2) * (2:ℝ) ^ (-x) := by
        rw [show -(1 + x) = -1 + (-x) by ring, Real.rpow_add (by norm_num), Real.rpow_neg_one]
        ring
      have e2 : (2:ℝ) ^ (1 - 2 * (1 + x)) ≤ (1/2) * (2:ℝ) ^ (-x) := by
        rw [show 1 - 2 * (1 + x) = -1 + (-2 * x) by ring, Real.rpow_add (by norm_num),
          Real.rpow_neg_one]
        have : (2:ℝ) ^ (-2 * x) ≤ (2:ℝ) ^ (-x) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        linarith
      rw [hy]; linarith
    have hbern2 := _root_.rpow_one_add_le_one_add_mul_self (s := y - 1) (by linarith)
      hinv0 (by rw [div_le_one (by linarith)]; linarith)
    rw [show 1 + (y - 1) = y by ring] at hbern2
    have hkey : 1 / (1 + x) * (x / 2) = 1 / (2 * p) := by
      rw [hx]; field_simp; ring
    have : 1 / (1 + x) * (y - 1) ≤ 1 / (1 + x) * (-(x / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hinv0
    linarith


lemma K_Sstar_nonneg (q s L j0 D : ℕ) (p B : ℝ) : 0 ≤ Sstar q s L j0 D p B := by
  unfold Sstar
  exact Finset.sum_nonneg (fun h _ => Real.iSup_nonneg (fun β => by positivity))

lemma K_ETail_nonneg (q s L P d : ℕ) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) : 0 ≤ ETail q s L P d g := by
  unfold ETail
  exact div_nonneg (Finset.sum_nonneg (fun τ _ => hg _)) (Nat.cast_nonneg _)

lemma K_errK_nonneg (q k : ℕ) : 0 ≤ errK q k := by
  unfold errK; split_ifs <;> positivity

lemma K_Wsum_nonneg (q : ℕ) (E : Finset ℕ) : 0 ≤ Wsum q E := by
  unfold Wsum; exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma K_varpi_nonneg (q s L j : ℕ) : 0 ≤ varpi q s L j := by
  unfold varpi
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (K_Wsum_nonneg _ _)

/-- If `W = 0`, then all weights are 0 and `A_k = 0`. -/
lemma K_Ak_zero (q s L P k : ℕ) (hW : Wsum q (Eset q (hL s L)) = 0) : Ak q s L P k = 0 := by
  have hwN : ∀ N, wN q s L N = 0 := by
    intro N
    unfold wN
    split_ifs with h
    · rfl
    · have hmem : xiN q L N ∈ (range (2 ^ q)).erase 0 :=
        mem_erase.2 ⟨h, mem_range.2 (ZMod.val_lt _)⟩
      unfold Wsum at hW
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun ξ _ => by positivity)).1 hW _ hmem
      simpa using this
  unfold Ak shAvg
  simp [hwN]

/-- If `A ≤ X` and `8 X (2^{δ'})^q ≤ 1`, then `A ≤ 2^{−δ'q}/8`. -/
lemma K_fin (A X δ' : ℝ) (q : ℕ) (hA : A ≤ X) (hX : 8 * X * ((2:ℝ) ^ δ') ^ q ≤ 1) :
    A ≤ (2:ℝ) ^ (-(δ' * q)) / 8 := by
  have hb : 0 < ((2:ℝ) ^ δ') ^ q := by positivity
  rw [Real.rpow_neg (by norm_num), Real.rpow_mul_natCast (by norm_num)]
  rw [le_div_iff₀ (by norm_num), ← one_div, le_div_iff₀ hb]
  nlinarith [mul_le_mul_of_nonneg_right hA hb.le]

/-- From `S ≤ (the bound of Definition 10.1)`: `S^{1/p} ≤ 200(q+2)²X((1 + r_c^p)^{1/p})^q`. -/
lemma K_root_bound (p q j0 : ℕ) (hp : 1 ≤ p) (hj : 2 * j0 < q) (X S : ℝ) (hX : 0 ≤ X) (hS : 0 ≤ S)
    (hb : ((1 + rc) / 2) ^ p ≤ 1/4) (hrc0 : 0 ≤ rc)
    (hSle : S ≤ ((q:ℝ) + 2) ^ ((2:ℝ) * ((p:ℝ) - 1)) * (4:ℝ) ^ (p:ℝ) * 25 * (2:ℝ) ^ ((p:ℝ) - 1) *
        X ^ (p:ℝ) * ((1 + rc ^ (p:ℝ)) ^ q + (2:ℝ) ^ q * ((1 + rc) / 2) ^ ((p:ℝ) * ((q:ℝ) - j0)))) :
    S ^ (1 / (p:ℝ)) ≤ 200 * ((q:ℝ) + 2) ^ 2 * X * ((1 + rc ^ p) ^ (1 / (p:ℝ))) ^ q := by
  have hb0 : 0 ≤ (1 + rc) / 2 := by positivity
  -- rewrite as powers with natural-number exponents
  have e1 : (2:ℝ) * ((p:ℝ) - 1) = ((2 * (p - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hp]; ring
  have e2 : (p:ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by push_cast [Nat.cast_sub hp]; ring
  have e3 : (p:ℝ) * ((q:ℝ) - j0) = ((p * (q - j0) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (show j0 ≤ q by omega)]; ring
  rw [e1, e2, e3, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast,
    Real.rpow_natCast, Real.rpow_natCast] at hSle
  -- the second term is at most 1
  have hsec : (2:ℝ) ^ q * ((1 + rc) / 2) ^ (p * (q - j0)) ≤ 1 := by
    rw [pow_mul]
    have h1 : (((1 + rc) / 2) ^ p) ^ (q - j0) ≤ (1/4 : ℝ) ^ (q - j0) :=
      pow_le_pow_left₀ (by positivity) hb _
    have h2 : (1/4 : ℝ) ^ (q - j0) ≤ (1/2 : ℝ) ^ q := by
      rw [show (1/4 : ℝ) = (1/2) ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : (2:ℝ) ^ q * (1/2 : ℝ) ^ q = 1 := by rw [← mul_pow]; norm_num
    have : (0:ℝ) ≤ 2 ^ q := by positivity
    nlinarith
  set W := (1 + rc ^ p) ^ q with hW
  have hrcp0 : 0 ≤ rc ^ p := by positivity
  have hW1 : 1 ≤ W := one_le_pow₀ (by linarith)
  have hQ : W + (2:ℝ) ^ q * ((1 + rc) / 2) ^ (p * (q - j0)) ≤ 2 * W := by linarith
  -- bound the whole by (200 (q+2)² X)^p W
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hq2 : (1:ℝ) ≤ (q:ℝ) + 2 := by linarith
  have hA : ((q:ℝ) + 2) ^ (2 * (p - 1)) * (4:ℝ) ^ p * 25 * (2:ℝ) ^ (p - 1) * X ^ p *
      (W + (2:ℝ) ^ q * ((1 + rc) / 2) ^ (p * (q - j0))) ≤ (200 * ((q:ℝ) + 2) ^ 2 * X) ^ p * W := by
    have f1 : ((q:ℝ) + 2) ^ (2 * (p - 1)) ≤ (((q:ℝ) + 2) ^ 2) ^ p := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hq2 (by omega)
    have f2 : (2:ℝ) ^ (p - 1) * 2 = 2 ^ p := by
      rw [← pow_succ]; congr 1; omega
    have f3 : (25:ℝ) ≤ 25 ^ p := by
      calc (25:ℝ) = 25 ^ 1 := by norm_num
        _ ≤ 25 ^ p := pow_le_pow_right₀ (by norm_num) hp
    have hXp : 0 ≤ X ^ p := pow_nonneg hX p
    have h4p : (0:ℝ) ≤ 4 ^ p := by positivity
    have h2p : (0:ℝ) ≤ 2 ^ (p - 1) := by positivity
    have hW0 : 0 ≤ W := by linarith
    calc ((q:ℝ) + 2) ^ (2 * (p - 1)) * (4:ℝ) ^ p * 25 * (2:ℝ) ^ (p - 1) * X ^ p *
          (W + (2:ℝ) ^ q * ((1 + rc) / 2) ^ (p * (q - j0)))
        ≤ (((q:ℝ) + 2) ^ 2) ^ p * (4:ℝ) ^ p * 25 * (2:ℝ) ^ (p - 1) * X ^ p * (2 * W) := by
          gcongr
      _ = (((q:ℝ) + 2) ^ 2) ^ p * (4:ℝ) ^ p * 25 * ((2:ℝ) ^ (p - 1) * 2) * X ^ p * W := by ring
      _ ≤ (((q:ℝ) + 2) ^ 2) ^ p * (4:ℝ) ^ p * 25 ^ p * (2:ℝ) ^ p * X ^ p * W := by
          rw [f2]; gcongr
      _ = (200 * ((q:ℝ) + 2) ^ 2 * X) ^ p * W := by
          rw [mul_pow, mul_pow, show (200:ℝ) ^ p = 4 ^ p * 25 ^ p * 2 ^ p by
            rw [← mul_pow, ← mul_pow]; norm_num]
          ring
  have hSle' := hSle.trans hA
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p:ℝ) ≠ 0 := by linarith
  have hY : 0 ≤ 200 * ((q:ℝ) + 2) ^ 2 * X := by positivity
  have hWn : 0 ≤ W := by linarith
  calc S ^ (1 / (p:ℝ)) ≤ ((200 * ((q:ℝ) + 2) ^ 2 * X) ^ p * W) ^ (1 / (p:ℝ)) :=
        Real.rpow_le_rpow hS hSle' (by positivity)
    _ = (200 * ((q:ℝ) + 2) ^ 2 * X) * W ^ (1 / (p:ℝ)) := by
        rw [Real.mul_rpow (by positivity) hWn, one_div, Real.pow_rpow_inv_natCast hY (by omega)]
    _ = 200 * ((q:ℝ) + 2) ^ 2 * X * ((1 + rc ^ p) ^ (1 / (p:ℝ))) ^ q := by
        rw [hW, ← Real.rpow_pow_comm (by positivity)]


/-- Rate of the second term: `Θ_*^{c_D/2} 2^{δ'} < 1`. -/
lemma K_rate2 (Θs w cD δ' : ℝ) (hΘ : Θs = 1 - w) (hw1 : w < 1) (hcD : 0 ≤ cD)
    (hδ' : δ' * Real.log 2 < cD * w / 2) :
    Θs ^ (cD / 2) * (2:ℝ) ^ δ' < 1 := by
  have hΘ0 : 0 < Θs := by linarith
  rw [Real.rpow_def_of_pos hΘ0, Real.rpow_def_of_pos (by norm_num), ← Real.exp_add,
    Real.exp_lt_one_iff]
  have hlog : Real.log Θs ≤ -w := by linarith [Real.log_le_sub_one_of_pos hΘ0]
  have := mul_le_mul_of_nonneg_right hlog (show 0 ≤ cD / 2 by positivity)
  nlinarith

/-- Rate of the third term: `2^{2δ²}(1 + r_c^p)^{1/p}Θ_φ^{c_D/2}2^{δ'} < 1`. -/
lemma K_rate3 (p : ℕ) (hp : 1 ≤ p) (Θφ w cD δ δ' : ℝ) (hΘ0 : 0 < Θφ) (hΘ : Θφ ≤ 1 - w / p)
    (hrc : rc ^ p ≤ cD * w / 4) (hcD : 0 ≤ cD)
    (hδ : (2 * δ ^ 2 + δ') * Real.log 2 < cD * w / (4 * p)) :
    (2:ℝ) ^ (2 * δ ^ 2) * (1 + rc ^ p) ^ (1 / (p:ℝ)) * Θφ ^ (cD / 2) * (2:ℝ) ^ δ' < 1 := by
  have hrc0 : 0 ≤ rc ^ p := pow_nonneg (by have := rc_bounds; linarith) p
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by linarith),
    Real.rpow_def_of_pos hΘ0, Real.rpow_def_of_pos (by norm_num), ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, Real.exp_lt_one_iff]
  have h1 : Real.log (1 + rc ^ p) ≤ rc ^ p := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + rc ^ p by linarith)]
  have h2 : Real.log Θφ ≤ -(w / p) := by linarith [Real.log_le_sub_one_of_pos hΘ0]
  have h1' : Real.log (1 + rc ^ p) * (1 / (p:ℝ)) ≤ cD * w / 4 * (1 / (p:ℝ)) :=
    mul_le_mul_of_nonneg_right (h1.trans hrc) (by positivity)
  have h2' : Real.log Θφ * (cD / 2) ≤ -(w / p) * (cD / 2) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have e : cD * w / 4 * (1 / (p:ℝ)) + -(w / p) * (cD / 2) = -(cD * w / (4 * p)) := by
    field_simp; ring
  nlinarith

/-- `l = log₂(1/Θ_*) ≥ w` (`Θ_* = 1 − w`, `0 < w < 1`). -/
lemma K_logb_ge (Θs w : ℝ) (hΘ : Θs = 1 - w) (hw0 : 0 < w) (hw1 : w < 1) :
    w ≤ Real.logb 2 (1 / Θs) := by
  have hΘ0 : 0 < Θs := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  rw [Real.logb, one_div, Real.log_inv, le_div_iff₀ hl2]
  have : Real.log Θs ≤ -w := by linarith [Real.log_le_sub_one_of_pos hΘ0]
  nlinarith


end Collatz.M1
