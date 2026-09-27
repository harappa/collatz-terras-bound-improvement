import CollatzProof.M1.S6
import CollatzProof.M1.K_Anal

/-!
# Auxiliary results for §14: the terms of step 4 of the proof of Proposition 14.1

The second, third and fourth terms of step 4 (shell 0 and the inner shells) of manuscript §14.2, and the condition `Y ≤ ⌊(s − q − 1)/2⌋` of step 2 (the outer shells),
are proved as inequalities for each slice. That they eventually hold (for large `q`) is provided by `K_core` in `S14.lean`.
-/

namespace Collatz.M1

open Finset Filter Topology

/-- From the window count and the comparison with `Θ`: `𝔼_τ γ^{N_D} ≤ 8(q+2)²(Θ^{c_D/2})^q`. -/
lemma K_window (q s L P : ℕ) (γ cD Θ : ℝ) (hγ1 : 1/2 ≤ γ) (hγ2 : γ ≤ 1) (hΘ34 : 3/4 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hD2 : 2 ≤ ⌊cD * q⌋₊) (hDt : ⌊cD * q⌋₊ ≤ s - P - 1) (hL0 : 0 ≤ hL s L)
    (hTne : (Tset q s L P).Nonempty) (hΘ : Theta γ (rhoBar q s L P) ≤ Θ)
    (hsP2 : ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) ≤ 4 * ((q:ℝ) + 2) ^ 2) :
    ETail q s L P ⌊cD * q⌋₊ (fun n => γ ^ n) ≤ 8 * ((q:ℝ) + 2) ^ 2 * (Θ ^ (cD / 2)) ^ q := by
  have hwc := window_count q s L P γ hγ1 hγ2 _ hD2 hDt hL0 hTne
  have hT0 : 0 ≤ Theta γ (rhoBar q s L P) := by
    linarith [K_theta_ge γ (rhoBar q s L P) hγ1 hγ2]
  have hΘm : Theta γ (rhoBar q s L P) ^ ((⌊cD * q⌋₊ - 1) / 2) ≤ Θ ^ ((⌊cD * q⌋₊ - 1) / 2) :=
    pow_le_pow_left₀ hT0 hΘ _
  have hΘp := K_pow_floor Θ cD hΘ34 hΘ1 q
  have hsP0 : 0 ≤ ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) := by positivity
  have hm0 : 0 ≤ Θ ^ ((⌊cD * q⌋₊ - 1) / 2) := pow_nonneg (by linarith) _
  calc _ ≤ _ := hwc
    _ ≤ ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) * Θ ^ ((⌊cD * q⌋₊ - 1) / 2) :=
        mul_le_mul_of_nonneg_left hΘm hsP0
    _ ≤ 4 * ((q:ℝ) + 2) ^ 2 * (2 * (Θ ^ (cD / 2)) ^ q) := mul_le_mul hsP2 hΘp hm0 (by positivity)
    _ = _ := by ring

/-- Second term: `𝔼_τ 2^{−N_D} ≤ 2^{−δ'q}/8`. -/
lemma K_term2 (q s L P : ℕ) (cD Θs δ' : ℝ) (hΘ34 : 3/4 ≤ Θs) (hΘ1 : Θs ≤ 1)
    (hD2 : 2 ≤ ⌊cD * q⌋₊) (hDt : ⌊cD * q⌋₊ ≤ s - P - 1) (hL0 : 0 ≤ hL s L)
    (hTne : (Tset q s L P).Nonempty) (hΘ : Theta (1/2) (rhoBar q s L P) ≤ Θs)
    (hsP2 : ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) ≤ 4 * ((q:ℝ) + 2) ^ 2)
    (hE : 64 * ((q:ℝ) + 2) ^ 2 * (Θs ^ (cD / 2) * (2:ℝ) ^ δ') ^ q ≤ 1) :
    ETail q s L P ⌊cD * q⌋₊ (fun n => (2:ℝ) ^ (-(n:ℝ))) ≤ (2:ℝ) ^ (-(δ' * q)) / 8 := by
  have hfun : (fun n : ℕ => (2:ℝ) ^ (-(n:ℝ))) = fun n => (1/2:ℝ) ^ n := by
    funext n; rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [hfun]
  apply K_fin _ _ δ' q (K_window q s L P (1/2) cD Θs (by norm_num) (by norm_num) hΘ34 hΘ1 hD2 hDt hL0
    hTne hΘ hsP2)
  rw [mul_pow] at hE
  linarith [show 8 * (8 * ((q:ℝ) + 2) ^ 2 * (Θs ^ (cD / 2)) ^ q) * ((2:ℝ) ^ δ') ^ q =
    64 * ((q:ℝ) + 2) ^ 2 * ((Θs ^ (cD / 2)) ^ q * ((2:ℝ) ^ δ') ^ q) by ring]

/-- Third term: `S_p^*(B)^{1/p} 𝔼_τ φ_p^{N_D} ≤ 2^{−δ'q}/8` (the bound `hSS` on `S_p^*` comes from Propositions 11.3 and 11.5, Corollary 12.2 and Proposition 12.4). -/
lemma K_term3 (q s L P j0 p : ℕ) (cD Θφ δ δ' : ℝ) (hp : 2 ≤ p) (hΘ34 : 3/4 ≤ Θφ) (hΘ1 : Θφ ≤ 1)
    (hD2 : 2 ≤ ⌊cD * q⌋₊) (hDt : ⌊cD * q⌋₊ ≤ s - P - 1) (hL0 : 0 ≤ hL s L)
    (hLup : hL s L ≤ 3.5 * δ ^ 2 * q) (hTne : (Tset q s L P).Nonempty)
    (hφ1 : 1/2 ≤ phiP p) (hφ2 : phiP p ≤ 1) (hΘ : Theta (phiP p) (rhoBar q s L P) ≤ Θφ)
    (hsP2 : ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) ≤ 4 * ((q:ℝ) + 2) ^ 2)
    (hj0 : 2 * j0 < q) (hbp : ((1 + rc) / 2) ^ p ≤ 1/4)
    (hSS : Sstar q s L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) ≤
      ((q:ℝ) + 2) ^ ((2:ℝ) * ((p:ℝ) - 1)) * (4:ℝ) ^ (p:ℝ) * 25 * (2:ℝ) ^ ((p:ℝ) - 1) *
        ((2:ℝ) ^ (tstar * hL s L + 1.1) * q * (q + 1)) ^ (p:ℝ) *
        ((1 + rc ^ (p:ℝ)) ^ q + (2:ℝ) ^ q * ((1 + rc) / 2) ^ ((p:ℝ) * ((q:ℝ) - j0))))
    (hE : 8 * (1600 * (2:ℝ) ^ (1.1:ℝ)) * ((q:ℝ) + 2) ^ 6 *
      ((2:ℝ) ^ (2 * δ ^ 2) * (1 + rc ^ p) ^ (1 / (p:ℝ)) * Θφ ^ (cD / 2) * (2:ℝ) ^ δ') ^ q ≤ 1) :
    Sstar q s L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) ^ (1 / (p:ℝ)) *
      ETail q s L P ⌊cD * q⌋₊ (fun n => phiP p ^ n) ≤ (2:ℝ) ^ (-(δ' * q)) / 8 := by
  obtain ⟨hts1, hts2⟩ := tstar_bounds
  obtain ⟨hr1, -⟩ := rc_bounds
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  set X := (2:ℝ) ^ (tstar * hL s L + 1.1) * q * (q + 1) with hX
  have hroot := K_root_bound p q j0 (by omega) hj0 X _ (by positivity) (K_Sstar_nonneg _ _ _ _ _ _ _)
    hbp (by linarith) hSS
  -- X ≤ 2^{1.1}(q+2)²(2^{2δ²})^q
  have hXle : X ≤ (2:ℝ) ^ (1.1:ℝ) * ((q:ℝ) + 2) ^ 2 * ((2:ℝ) ^ (2 * δ ^ 2)) ^ q := by
    have h1 : tstar * hL s L ≤ 2 * δ ^ 2 * q := by
      have : tstar * hL s L ≤ 0.4881 * (3.5 * δ ^ 2 * q) :=
        mul_le_mul hts2.le hLup hL0 (by norm_num)
      have : 0 ≤ δ ^ 2 * q := by positivity
      linarith
    have h2 : (2:ℝ) ^ (tstar * hL s L) ≤ ((2:ℝ) ^ (2 * δ ^ 2)) ^ q := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    have h3 : (q:ℝ) * (q + 1) ≤ ((q:ℝ) + 2) ^ 2 := by nlinarith
    rw [hX, Real.rpow_add (by norm_num)]
    calc (2:ℝ) ^ (tstar * hL s L) * 2 ^ (1.1:ℝ) * q * (q + 1)
        = (2:ℝ) ^ (1.1:ℝ) * ((q:ℝ) * (q + 1)) * (2:ℝ) ^ (tstar * hL s L) := by ring
      _ ≤ (2:ℝ) ^ (1.1:ℝ) * ((q:ℝ) + 2) ^ 2 * ((2:ℝ) ^ (2 * δ ^ 2)) ^ q := by gcongr
  have hwin := K_window q s L P (phiP p) cD Θφ hφ1 hφ2 hΘ34 hΘ1 hD2 hDt hL0 hTne hΘ hsP2
  have hET0 : 0 ≤ ETail q s L P ⌊cD * q⌋₊ (fun n => phiP p ^ n) := by
    unfold ETail
    exact div_nonneg (Finset.sum_nonneg (fun τ _ => pow_nonneg (by linarith) _)) (Nat.cast_nonneg _)
  set ρ1 := (1 + rc ^ p) ^ (1 / (p:ℝ)) with hρ1
  set ϑ := Θφ ^ (cD / 2) with hϑ
  have hρ10 : 0 ≤ ρ1 := by positivity
  have hϑ0 : 0 ≤ ϑ := by rw [hϑ]; exact Real.rpow_nonneg (by linarith) _
  apply K_fin _ (1600 * (2:ℝ) ^ (1.1:ℝ) * ((q:ℝ) + 2) ^ 6 * ((2:ℝ) ^ (2 * δ ^ 2) * ρ1 * ϑ) ^ q) δ' q
  · have hS1 : Sstar q s L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) ^ (1 / (p:ℝ)) ≤
        200 * ((q:ℝ) + 2) ^ 2 * ((2:ℝ) ^ (1.1:ℝ) * ((q:ℝ) + 2) ^ 2 * ((2:ℝ) ^ (2 * δ ^ 2)) ^ q) *
          ρ1 ^ q := by
      refine hroot.trans ?_
      gcongr
    calc _ ≤ (200 * ((q:ℝ) + 2) ^ 2 * ((2:ℝ) ^ (1.1:ℝ) * ((q:ℝ) + 2) ^ 2 *
            ((2:ℝ) ^ (2 * δ ^ 2)) ^ q) * ρ1 ^ q) * (8 * ((q:ℝ) + 2) ^ 2 * ϑ ^ q) :=
          mul_le_mul hS1 hwin hET0 (by positivity)
      _ = _ := by rw [mul_pow, mul_pow]; ring
  · rw [mul_pow] at hE
    linarith [show 8 * (1600 * (2:ℝ) ^ (1.1:ℝ) * ((q:ℝ) + 2) ^ 6 * ((2:ℝ) ^ (2 * δ ^ 2) * ρ1 * ϑ) ^ q) *
      ((2:ℝ) ^ δ') ^ q = 8 * (1600 * (2:ℝ) ^ (1.1:ℝ)) * ((q:ℝ) + 2) ^ 6 *
      (((2:ℝ) ^ (2 * δ ^ 2) * ρ1 * ϑ) ^ q * ((2:ℝ) ^ δ') ^ q) by ring]

/-- `Y ≥ 0` and `Y ≤ (δ'q + 3 + 2 log₂ q)/l`. -/
lemma K_Yout_le (q s : ℕ) (δ' Θs l : ℝ) (hl : l = Real.logb 2 (1 / Θs)) (hl0 : 0 < l) (hδ' : 0 ≤ δ')
    (hs1 : 1 ≤ s) (hs2q : (s:ℝ) ≤ 2 * q) :
    0 ≤ Yout δ' Θs s q ∧ Yout δ' Θs s q ≤ (δ' * q + 3 + 2 * Real.logb 2 q) / l := by
  have hs1' : (1:ℝ) ≤ s := by exact_mod_cast hs1
  have hq0 : (0:ℝ) < q := by linarith
  have hlogs0 : 0 ≤ Real.logb 2 s := Real.logb_nonneg (by norm_num) hs1'
  have hlogs : Real.logb 2 s ≤ 1 + Real.logb 2 q := by
    calc Real.logb 2 s ≤ Real.logb 2 (2 * q) :=
          Real.logb_le_logb_of_le (by norm_num) (by linarith) hs2q
      _ = 1 + Real.logb 2 q := by
          rw [Real.logb_mul (by norm_num) hq0.ne', Real.logb_self_eq_one (by norm_num)]
  unfold Yout
  rw [← hl]
  constructor
  · apply div_nonneg _ hl0.le
    have : 0 ≤ δ' * q := by positivity
    linarith
  · apply div_le_div_of_nonneg_right _ hl0.le
    linarith

/-- Fourth term: if `k < k₁`, then `err_k ≤ 2^{−δ'q}/8`. -/
lemma K_term4 (q s k : ℕ) (δ' Θs l : ℝ) (hl : l = Real.logb 2 (1 / Θs)) (hl0 : 0 < l)
    (hδ' : 0 ≤ δ') (hs1 : 1 ≤ s) (hs2q : (s:ℝ) ≤ 2 * q) (hk : k < k1out δ' Θs s q)
    (hE : Real.logb 2 (18 * Real.pi) + 8 + 6 / l + (1 + 4 / l) * Real.logb 2 q ≤
      (1 - 2 * δ' - 2 * δ' / l) * q) :
    errK q k ≤ (2:ℝ) ^ (-(δ' * q)) / 8 := by
  have hs1' : (1:ℝ) ≤ s := by exact_mod_cast hs1
  have hq0 : (0:ℝ) < q := by linarith
  obtain ⟨hY0, hY⟩ := K_Yout_le q s δ' Θs l hl hl0 hδ' hs1 hs2q
  set Y := Yout δ' Θs s q with hYdef
  have hX0 : 0 ≤ δ' * q + 5 + 2 * Y := by positivity
  have h9 := K_k1out_le δ' Θs s q hX0
  have h3 : (3:ℝ) ^ (k + 1) ≤ 3 ^ (k1out δ' Θs s q) := pow_le_pow_right₀ (by norm_num) hk
  have he := K_errK_le q k
  -- bring everything to powers of 2
  have hpos : 0 < 18 * Real.pi * q := by positivity
  have hmain : 2 * Real.pi * q * (9 * (2:ℝ) ^ (δ' * q + 5 + 2 * Y)) * (1/2) ^ q ≤
      (2:ℝ) ^ (-(δ' * q)) / 8 := by
    have e1 : 2 * Real.pi * q * (9 * (2:ℝ) ^ (δ' * q + 5 + 2 * Y)) * (1/2) ^ q =
        (2:ℝ) ^ (Real.logb 2 (18 * Real.pi * q) + (δ' * q + 5 + 2 * Y) - q) := by
      rw [show Real.logb 2 (18 * Real.pi * q) + (δ' * q + 5 + 2 * Y) - q =
          Real.logb 2 (18 * Real.pi * q) + ((δ' * q + 5 + 2 * Y) - q) by ring,
        Real.rpow_add (by norm_num) (Real.logb 2 (18 * Real.pi * q)),
        Real.rpow_logb (by norm_num) (by norm_num) hpos,
        Real.rpow_sub (by norm_num) (δ' * q + 5 + 2 * Y), Real.rpow_natCast, one_div, inv_pow]
      field_simp
      ring
    have e2 : (2:ℝ) ^ (-(δ' * q)) / 8 = (2:ℝ) ^ (-(δ' * q) - 3) := by
      rw [Real.rpow_sub (by norm_num)]; norm_num
    rw [e1, e2]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [Real.logb_mul (by positivity) hq0.ne']
    have hY2 : 2 * Y ≤ 2 * δ' / l * q + 6 / l + 4 / l * Real.logb 2 q := by
      have : 2 * ((δ' * q + 3 + 2 * Real.logb 2 q) / l) =
          2 * δ' / l * q + 6 / l + 4 / l * Real.logb 2 q := by field_simp; ring
      linarith
    have hE' : Real.logb 2 (18 * Real.pi) + 8 + 6 / l + (Real.logb 2 q + 4 / l * Real.logb 2 q) ≤
        q - 2 * δ' * q - 2 * δ' / l * q := by
      have e3 : (1 - 2 * δ' - 2 * δ' / l) * q = q - 2 * δ' * q - 2 * δ' / l * q := by ring
      have e4 : (1 + 4 / l) * Real.logb 2 q = Real.logb 2 q + 4 / l * Real.logb 2 q := by ring
      linarith
    linarith
  calc errK q k ≤ 2 * Real.pi * q * 3 ^ (k + 1) * (1/2) ^ q := he
    _ ≤ 2 * Real.pi * q * (9 * (2:ℝ) ^ (δ' * q + 5 + 2 * Y)) * (1/2) ^ q := by
        gcongr; exact h3.trans h9
    _ ≤ _ := hmain

/-- The outer-shell condition `Y ≤ ⌊(s − q − 1)/2⌋`. -/
lemma K_Yout_cond (q s : ℕ) (δ' Θs l η : ℝ) (hl : l = Real.logb 2 (1 / Θs)) (hl19 : 0.19 ≤ l)
    (hδ' : 0 ≤ δ') (hs1 : 1 ≤ s) (hs2q : (s:ℝ) ≤ 2 * q) (hηq : η * q ≤ (s:ℝ) - q) (hqs : q + 1 < s)
    (hE : 3 + 0.19 + 2 * Real.logb 2 q ≤ (0.095 * η - δ') * q) :
    Yout δ' Θs s q ≤ ((s - q - 1) / 2 : ℕ) := by
  have hl0 : 0 < l := by linarith
  have hs1' : (1:ℝ) ≤ s := by exact_mod_cast hs1
  have hq0 : (0:ℝ) < q := by linarith
  obtain ⟨-, hY⟩ := K_Yout_le q s δ' Θs l hl hl0 hδ' hs1 hs2q
  have hq1 : 0 < q := Nat.cast_pos.mp hq0
  have hq1' : (1:ℝ) ≤ q := by exact_mod_cast hq1
  have hlogq : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) hq1'
  set R := (η * q - 2) / 2 with hR
  have hδq : 0 ≤ δ' * q := by positivity
  have hR0 : 0 ≤ R := by rw [hR]; nlinarith
  have h1 : (δ' * q + 3 + 2 * Real.logb 2 q) / l ≤ R := by
    rw [div_le_iff₀ hl0]
    have : 0.19 * R ≤ l * R := mul_le_mul_of_nonneg_right hl19 hR0
    rw [hR] at this ⊢
    nlinarith
  have h2 : 2 * ((s - q - 1) / 2) + 2 ≥ s - q := by omega
  have h2' : (2:ℝ) * (((s - q - 1) / 2 : ℕ) : ℝ) + 2 ≥ ((s - q : ℕ) : ℝ) := by exact_mod_cast h2
  rw [Nat.cast_sub (by omega)] at h2'
  have : R ≤ (((s - q - 1) / 2 : ℕ) : ℝ) := by rw [hR]; linarith
  linarith


end Collatz.M1
