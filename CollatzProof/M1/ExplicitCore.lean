import CollatzProof.M1.S14
import CollatzProof.M1.ExplicitNum

/-!
# Explicit values of the main theorem (version 2 of the proof manuscript): Proposition 14.1 with explicit constants

`K_core` and `all_shells` in `S14.lean` choose the constants by a qualitative rule (`ρ♯ = ρ_c + 1/10`, `δ = min(10^{−5}, η/100, c_D w/(20p))`, `δ' = 3δ`).
Here the same assembly is done with the constants of §14.1 of version 2 of the proof manuscript (`c_D = 9×10^{−4}`, `p = 312`, `ρ♯ = ρ_c + 10^{−4}`, `δ = 2.8055×10^{−7}`, `δ' = 2.5δ`;
the constants of revision r6 of the paper). The outline of the assembly is that of `K_core`, and the components (`choose_j0`, `outer_shells`, `hgt`, `holder`, `Sstar_bound`,
`K_term2` to `K_term4`, `K_Yout_cond`) are used unchanged. Three things are changed:
- `K_core_param` takes the constants as hypotheses (making explicit which numerical inequalities are needed).
- The closeness of `ρ̄` (Lemma 6.4) is `ε_ρ ≤ 10^{−4}` (Lemma 14.0 (f) of the manuscript). Hence the `η` in `s − q ≥ ηq` must satisfy `1.23δ < 1.5849×10^{−4}η`,
  and `η = 2α − 1` of `all_shells` is not enough when `α` is close to `1/2`. `all_shells_explicit` passes `η = β_α − 1 = (2α − 1)/(1 − α)`
  (`s > αK` gives `s − q > (β_α − 1)q`).
- The rate of the third term (`X_rate3` instead of `K_rate3`) is shown from `log(1 + r_c^p) ≤ r_c^p`, `log Θ_φ ≤ Θ_φ − 1` and the precise numerical values of `ExplicitNum.lean`.

**General form** (for version 3 of the proof manuscript): `K_core_paramG` takes as arguments the constants `(a, b)` of `R_δ` (`RdeltaG a b δ`), the factor `2^E` in the rate of the third term,
and the supply `HgtSupply c_D` of the lattice condition (the form of the conclusion of Proposition 13.2). `K_core_param` of version 2 is kept, with an unchanged statement, as its special case with `(a, b, E) = (1.23, 3.5, 2δ²)` and
`hgt` (Theorem 2). Version 3 uses `(1.38, 4.48, 2.2δ²)` and `hgt_thm1` (Theorem 1; `ExplicitV3.lean`).
-/

namespace Collatz.M1

open Finset Filter Topology

/-- The rate of the third term (precise version, general form): if `Θ_φ ≤ 1 − v`, `r_c^p ≤ R` and `(E + δ') log 2 + R/p < c_D v/2`, then
`2^E(1 + r_c^p)^{1/p}Θ_φ^{c_D/2}2^{δ'} < 1`. -/
lemma X_rate3G (p : ℕ) (hp : 1 ≤ p) (Θφ v R cD E δ' : ℝ) (hΘ0 : 0 < Θφ) (hΘ : Θφ ≤ 1 - v)
    (hrc : rc ^ p ≤ R) (hcD : 0 ≤ cD)
    (hδ : (E + δ') * Real.log 2 + R / p < cD * v / 2) :
    (2:ℝ) ^ E * (1 + rc ^ p) ^ (1 / (p:ℝ)) * Θφ ^ (cD / 2) * (2:ℝ) ^ δ' < 1 := by
  have hrc0 : 0 ≤ rc ^ p := pow_nonneg (by have := rc_bounds; linarith) p
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by linarith),
    Real.rpow_def_of_pos hΘ0, Real.rpow_def_of_pos (by norm_num), ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, Real.exp_lt_one_iff]
  have h1 : Real.log (1 + rc ^ p) ≤ R := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + rc ^ p by linarith)]
  have h2 : Real.log Θφ ≤ -v := by linarith [Real.log_le_sub_one_of_pos hΘ0]
  have h1' : Real.log (1 + rc ^ p) * (1 / (p:ℝ)) ≤ R / p := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right h1 hp0.le
  have h2' : Real.log Θφ * (cD / 2) ≤ -v * (cD / 2) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  nlinarith

/-- The rate of the third term (precise version): if `Θ_φ ≤ 1 − v`, `r_c^p ≤ R` and `(2δ² + δ') log 2 + R/p < c_D v/2`, then
`2^{2δ²}(1 + r_c^p)^{1/p}Θ_φ^{c_D/2}2^{δ'} < 1`. -/
lemma X_rate3 (p : ℕ) (hp : 1 ≤ p) (Θφ v R cD δ δ' : ℝ) (hΘ0 : 0 < Θφ) (hΘ : Θφ ≤ 1 - v)
    (hrc : rc ^ p ≤ R) (hcD : 0 ≤ cD)
    (hδ : (2 * δ ^ 2 + δ') * Real.log 2 + R / p < cD * v / 2) :
    (2:ℝ) ^ (2 * δ ^ 2) * (1 + rc ^ p) ^ (1 / (p:ℝ)) * Θφ ^ (cD / 2) * (2:ℝ) ^ δ' < 1 :=
  X_rate3G p hp Θφ v R cD (2 * δ ^ 2) δ' hΘ0 hΘ hrc hcD hδ

set_option maxHeartbeats 2000000 in
/-- General form of the core of Proposition 14.1 (`RdeltaG a b δ`; the supply `hH` of the lattice condition and the constants are taken as hypotheses): with `ρ♯ = ρ_c + 10^{−4}`,
if `δ, δ', c_D, p` satisfy the numerical conditions, then, for `q` sufficiently large with `1 < s/q ≤ 1.94` and `s − q ≥ ηq`, `A_k ≤ 2^{−δ'q}` for every slice
and every shell. `E` gives the factor `2^E` in the rate of the third term (`t* h_L ≤ Eq`, from `t* < 0.4881` and `h_L ≤ bδ²q`).
Correspondence of the conditions with Lemma 14.0 of the manuscript (Lemma 16.1 of the paper): `h3` is (b) (`κ_eff > 0`), `h2` is (d), `hδ'η` is (e), `hηρ` is (f), `hcDη` and `hbp` are (g).
Version 2 has `(a, b, E) = (1.23, 3.5, 2δ²)` (`K_core_param`), version 3 has `(1.38, 4.48, 2.2δ²)` (`ExplicitV3.lean`; §14.6.2 of version 3 of the manuscript). -/
theorem K_core_paramG (a b E η δ δ' cD v R : ℝ) (p : ℕ) (hH : HgtSupply cD)
    (hδ0 : 0 < δ) (haδ : a * δ ≤ 1.23e-3) (hba : b * δ ≤ a) (hbδ : b * δ ^ 2 ≤ 1e-8)
    (hE : 0.4881 * (b * δ ^ 2) ≤ E) (hδ'0 : 0 < δ') (hδ'c : δ' ≤ 1e-3)
    (hcD0 : 0 < cD) (hcDη : cD ≤ η / 2)
    (hp2 : 2 ≤ p) (hbp : ((1 + rc) / 2) ^ p ≤ 1/4) (hrcp : rc ^ p ≤ R)
    (hv : Theta (phiP p) (rhoc + 1e-4) ≤ 1 - v)
    (h3 : (E + δ') * Real.log 2 + R / p < cD * v / 2)
    (h2 : δ' * 0.7 < cD * 0.2328 / 2)
    (hδ'η : δ' < 0.095 * η)
    (hηρ : a * δ < 1.5849e-4 * η) :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s:ℝ) / q →
      (s:ℝ) / q ≤ 1.94 → η * q ≤ (s:ℝ) - q →
      ∀ L P, RdeltaG a b δ s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q)) := by
  obtain ⟨hrc1, hrc2⟩ := rhoc_bounds
  obtain ⟨hr1, hr2⟩ := rc_bounds
  obtain ⟨hcc1, -⟩ := cc_bounds
  have hlog2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
  have hη : 0 < η := by linarith
  -- ρ♯ = ρ_c + 10^{−4}, w = ρ♯(1 − ρ♯), Θ_* = Θ_{1/2}(ρ♯) = 1 − w, l = log₂(1/Θ_*)
  obtain ⟨ρs, hρs⟩ : ∃ x : ℝ, x = rhoc + 1e-4 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ x : ℝ, x = ρs * (1 - ρs) := ⟨_, rfl⟩
  obtain ⟨hw1, hw2⟩ := X_w_bounds
  rw [← hρs, ← hw] at hw1 hw2
  have hρs1 : rhoc + 1e-4 ≤ 1 := by linarith
  obtain ⟨Θs, hΘs⟩ : ∃ x : ℝ, x = Theta (1/2) ρs := ⟨_, rfl⟩
  have hΘs_eq : Θs = 1 - w := by rw [hΘs, hw, Theta]; ring
  have hΘs0 : 0 < Θs := by linarith
  have hΘs1 : Θs < 1 := by linarith
  have hΘs34 : 3/4 ≤ Θs := by linarith
  obtain ⟨l, hl⟩ : ∃ x : ℝ, x = Real.logb 2 (1 / Θs) := ⟨_, rfl⟩
  have hl19 : 0.19 ≤ l := by
    rw [hl]; linarith [K_logb_ge Θs w hΘs_eq (by linarith) (by linarith)]
  have hl0 : 0 < l := by linarith
  -- the Hölder exponent p
  have hp0 : (0:ℝ) < p := by positivity
  have hp2' : (2:ℝ) ≤ p := by exact_mod_cast hp2
  obtain ⟨hφ1, hφ2⟩ := K_phiP p hp2
  have hφ1' : phiP p ≤ 1 := by linarith [show (0:ℝ) ≤ 1 / (2 * p) by positivity]
  obtain ⟨Θφ, hΘφ⟩ : ∃ x : ℝ, x = Theta (phiP p) ρs := ⟨_, rfl⟩
  have hΘφ34 : 3/4 ≤ Θφ := hΘφ ▸ K_theta_ge _ _ hφ1 hφ1'
  have hΘφ_le : Θφ ≤ 1 - v := by rw [hΘφ, hρs]; exact hv
  have hΘφ1 : Θφ ≤ 1 := by rw [hΘφ, Theta]; nlinarith
  have hδ'cc : δ' < cc / 2 := lt_of_le_of_lt hδ'c (by linarith)
  -- rates
  have hu2 : Θs ^ (cD / 2) * (2:ℝ) ^ δ' < 1 := by
    refine K_rate2 Θs w cD δ' hΘs_eq (by linarith) hcD0.le ?_
    have a1 : δ' * Real.log 2 ≤ δ' * 0.7 := mul_le_mul_of_nonneg_left hlog2.le hδ'0.le
    have a2 : cD * 0.2328 ≤ cD * w := mul_le_mul_of_nonneg_left hw1 hcD0.le
    linarith
  have hu3 : (2:ℝ) ^ E * (1 + rc ^ p) ^ (1 / (p:ℝ)) * Θφ ^ (cD / 2) *
      (2:ℝ) ^ δ' < 1 :=
    X_rate3G p (by omega) Θφ v R cD E δ' (by linarith) hΘφ_le hrcp hcD0.le h3
  have hc4 : 0 < 1 - 2 * δ' - 2 * δ' / l := by
    have : 2 * δ' / l ≤ 2 * δ' / 0.19 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hl19
    have h2' : 2 * δ' / (0.19:ℝ) ≤ 2 * 1e-3 / 0.19 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have h3' : 2 * (1e-3:ℝ) / 0.19 < 0.5 := by norm_num
    linarith
  -- thresholds of the components
  obtain ⟨qj, hj⟩ := choose_j0G a b δ δ' (by linarith)
  obtain ⟨qo, ho⟩ := outer_shellsG a b δ δ' Θs haδ hδ'0 hΘs0 hΘs1
  obtain ⟨qh, hh⟩ := hH
  -- the inequalities that eventually hold
  have ev := ((((((((eventually_ge_atTop (max (max 20 qj) (max qo qh))).and
    (K_ev_lin (2 / cD) 1 one_pos)).and
    (K_ev_lin (2 / η) 1 one_pos)).and
    (K_ev_lin 0.6 (1.5849e-4 * η - a * δ) (by linarith))).and
    (K_ev_log (3 + 0.19) 2 (0.095 * η - δ') (sub_pos.2 hδ'η))).and
    (K_ev_small 64 2 _ (by positivity) hu2)).and
    (K_ev_small (8 * (1600 * (2:ℝ) ^ (1.1:ℝ))) 6 _ (by positivity) hu3)).and
    (K_ev_log (Real.logb 2 (18 * Real.pi) + 8 + 6 / l) (1 + 4 / l) _ hc4))
  obtain ⟨q0, hq0⟩ := eventually_atTop.mp ev
  refine ⟨q0, fun s q hq hsq1 hsq2 hηq => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨hqmax, hED⟩, hEq1⟩, hErho⟩, hEY⟩, hE2⟩, hE3⟩, hE4⟩ := hq0 q hq
  have h20 : 20 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hqmax
  have hqj : qj ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hqmax
  have hqo : qo ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hqmax
  have hqh : qh ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hqmax
  have hq20 : (20:ℝ) ≤ q := by exact_mod_cast h20
  have hqpos : (0:ℝ) < q := by linarith
  have hs2q : (s:ℝ) ≤ 2 * q := by
    have := (div_le_iff₀ hqpos).1 hsq2; linarith
  have hηq1 : 2 ≤ η * q := by
    have := hEq1; rw [one_mul, div_le_iff₀ hη] at this; linarith
  have hqs : q + 1 < s := by
    have : (q:ℝ) + 1 < s := by linarith
    exact_mod_cast this
  have hs1 : 1 ≤ s := by omega
  -- ρ̄ is closer to ρ_c than ρ♯ is (Lemma 6.4; Lemma 14.0 (f) of the manuscript: ε_ρ ≤ 10^{−4})
  have hΘall : ∀ γ : ℝ, γ ≤ 1 → ∀ L P, RdeltaG a b δ s q L P →
      Theta γ (rhoBar q s L P) ≤ Theta γ ρs := by
    intro γ hγ L P hR
    obtain ⟨hrb, -⟩ := rhoBar_closeG a b δ s q L P hδ0.le hba hqs hR
    have hε : (a * δ * q + aa) / (lam * (s - q - 1)) ≤ 1e-4 := by
      have hlam := lam_bounds
      have hpos : 0 < lam * ((s:ℝ) - q - 1) := by
        apply mul_pos (by linarith); linarith
      rw [div_le_iff₀ hpos]
      have ha : aa < 0.586 := by unfold aa; linarith
      have hsq' : η * q - 1 ≤ (s:ℝ) - q - 1 := by linarith
      have h158 : 1.5849 * (η * q - 1) ≤ lam * ((s:ℝ) - q - 1) :=
        mul_le_mul (by linarith) hsq' (by linarith) (by linarith)
      have : 0.6 ≤ (1.5849e-4 * η - a * δ) * q := hErho
      linarith
    rw [hρs]
    exact Theta_le_of_close γ _ 1e-4 hγ (by norm_num) hρs1 (hrb.trans hε)
  have hYout := K_Yout_cond q s δ' Θs l η hl hl19 hδ'0.le hs1 hs2q hηq hqs hEY
  intro L P hR k hk
  obtain ⟨hL0, hLup, -, -, -, hTne, -⟩ := id hR
  have hLsmall : hL s L ≤ 1e-8 * q := hLup.trans (mul_le_mul_of_nonneg_right hbδ hqpos.le)
  have htL : tstar * hL s L ≤ E * q := by
    obtain ⟨-, hts2⟩ := tstar_bounds
    have h1 : tstar * hL s L ≤ 0.4881 * hL s L := mul_le_mul_of_nonneg_right hts2.le hL0
    have h2 : 0.4881 * hL s L ≤ 0.4881 * (b * δ ^ 2 * q) :=
      mul_le_mul_of_nonneg_left hLup (by norm_num)
    have h3 : 0.4881 * (b * δ ^ 2) * q ≤ E * q := mul_le_mul_of_nonneg_right hE hqpos.le
    linarith
  -- outer shells (Proposition 9.2)
  by_cases hk1 : k1out δ' Θs s q ≤ k
  · refine ho s q hqo hsq1 hsq2 (fun L P hR => ?_) hYout L P hR k hk1 hk
    have := hΘall (1/2) (by norm_num) L P hR
    rwa [← hΘs] at this
  -- shell 0 and the inner shells (Lemma 7.4, Proposition 10.2)
  push Not at hk1
  obtain ⟨j0, hj0q, hvar, hE⟩ := hj s q L P hqj hsq1 hsq2 hR
  rcases (K_Wsum_nonneg q (Eset q (hL s L))).eq_or_lt with hW0 | hWpos
  · rw [K_Ak_zero q s L P k hW0.symm]; positivity
  obtain ⟨-, hsP⟩ := rhoBar_closeG a b δ s q L P hδ0.le hba hqs hR
  have hD2 : 2 ≤ ⌊cD * q⌋₊ := by
    apply Nat.le_floor
    have := hED; rw [one_mul, div_le_iff₀ hcD0] at this
    push_cast; linarith
  have hDt : ⌊cD * q⌋₊ ≤ s - P - 1 := by
    have h1 : (⌊cD * q⌋₊ : ℝ) ≤ cD * q := Nat.floor_le (by positivity)
    have h2 : (⌊cD * q⌋₊ : ℝ) ≤ ((s - q : ℕ) : ℝ) := by
      have h3 : cD * q ≤ η / 2 * q := mul_le_mul_of_nonneg_right hcDη hqpos.le
      rw [Nat.cast_sub (by omega)]; linarith
    have : ⌊cD * q⌋₊ ≤ s - q := by exact_mod_cast h2
    omega
  have hpow1 : (2:ℝ) ^ (-(δ' * q)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.2 (by positivity))
  have hvar2 : varpi q s L j0 ≤ (2:ℝ) ^ (-(δ' * q)) / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one] at hvar; exact hvar
  have hvar_half : varpi q s L j0 ≤ 1 / 2 := by linarith
  have hvar0 := K_varpi_nonneg q s L j0
  have hhold := holderG a b δ s q L P j0 ⌊cD * q⌋₊ k (p:ℝ) hsq2 h20 hR hD2 hp2' hk
    (by linarith) hWpos
  have hsplit := split_depth q s L P k j0 (by omega)
  have hsP2 : ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) ≤ 4 * ((q:ℝ) + 2) ^ 2 := by
    have a1 : ((s - P : ℕ) : ℝ) ≤ 2 * q := le_trans (by exact_mod_cast Nat.sub_le s P) hs2q
    have a2 : ((s - P - 1 : ℕ) : ℝ) ≤ 2 * q :=
      le_trans (by exact_mod_cast (Nat.sub_le _ _).trans (Nat.sub_le s P)) hs2q
    calc ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) ≤ (2 * q) * (2 * q) :=
          mul_le_mul a1 a2 (Nat.cast_nonneg _) (by positivity)
      _ ≤ 4 * ((q:ℝ) + 2) ^ 2 := by linarith only [hqpos]
  -- the 2nd, 3rd and 4th terms
  have hT2 := K_term2 q s L P cD Θs δ' hΘs34 hΘs1.le hD2 hDt hL0 hTne
    (by rw [hΘs]; exact hΘall _ (by norm_num) L P hR) hsP2 hE2
  have hSS := Sstar_bound s q L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) hp2' (by omega) h20
    (by positivity) hL0 hE hvar_half (by omega) (hh s q L hqh hsq1 hsq2 hL0 hLsmall)
  have hT3 := K_term3G q s L P j0 p cD Θφ E δ' hp2 hΘφ34 hΘφ1 hD2 hDt hL0 htL hTne hφ1 hφ1'
    (by rw [hΘφ]; exact hΘall _ hφ1' L P hR) hsP2 hj0q hbp hSS hE3
  have hT4 := K_term4 q s k δ' Θs l hl hl0 hδ'0.le hs1 hs2q hk1 hE4
  -- conclusion
  have hRHS0 : 0 ≤ ETail q s L P ⌊cD * q⌋₊ (fun n => (2:ℝ) ^ (-(n:ℝ))) +
      Sstar q s L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) ^ (1 / (p:ℝ)) *
        ETail q s L P ⌊cD * q⌋₊ (fun n => phiP p ^ n) + errK q k := by
    have := K_ETail_nonneg q s L P ⌊cD * q⌋₊ (fun n => (2:ℝ) ^ (-(n:ℝ))) (fun n => by positivity)
    have := K_ETail_nonneg q s L P ⌊cD * q⌋₊ (fun n => phiP p ^ n)
      (fun n => pow_nonneg (by linarith) _)
    have := K_errK_nonneg q k
    have : 0 ≤ Sstar q s L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) ^ (1 / (p:ℝ)) :=
      Real.rpow_nonneg (K_Sstar_nonneg _ _ _ _ _ _ _) _
    positivity
  have hdeep : AkDeep q s L P k j0 ≤ ETail q s L P ⌊cD * q⌋₊ (fun n => (2:ℝ) ^ (-(n:ℝ))) +
      Sstar q s L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) ^ (1 / (p:ℝ)) *
        ETail q s L P ⌊cD * q⌋₊ (fun n => phiP p ^ n) + errK q k := by
    have h1v : 0 < 1 - varpi q s L j0 := by linarith
    have := mul_le_mul_of_nonneg_right hhold h1v.le
    rw [div_mul_cancel₀ _ h1v.ne'] at this
    exact this.trans (mul_le_of_le_one_right hRHS0 (by linarith only [hvar0]))
  have hpos2 : (0:ℝ) < (2:ℝ) ^ (-(δ' * q)) := by positivity
  linarith only [hsplit, hdeep, hvar2, hT2, hT3, hT4, hpos2]

set_option maxHeartbeats 1000000 in
/-- The core of Proposition 14.1 (the constants taken as hypotheses): with `ρ♯ = ρ_c + 10^{−4}`, if `δ, δ', c_D, p` satisfy the numerical conditions, then,
for `q` sufficiently large with `1 < s/q ≤ 1.94` and `s − q ≥ ηq`, `A_k ≤ 2^{−δ'q}` for every slice of `R_δ` and every shell.
Correspondence of the conditions with Lemma 14.0 of the manuscript: `h3` is (b) (`κ_eff > 0`), `h2` is (d), `hδ'η` is (e), `hηρ` is (f), `hcDη` and `hbp` are (g). -/
theorem K_core_param (hBug : BugeaudHyp) (η δ δ' cD v R : ℝ) (p : ℕ)
    (hδ0 : 0 < δ) (hδ5 : δ ≤ 1e-5) (hδδ' : 2 * δ < δ') (hδ'c : δ' ≤ 1e-3)
    (hcD0 : 0 < cD) (hcD1 : cD ≤ 9e-4) (hcDη : cD ≤ η / 2)
    (hp2 : 2 ≤ p) (hbp : ((1 + rc) / 2) ^ p ≤ 1/4) (hrcp : rc ^ p ≤ R)
    (hv : Theta (phiP p) (rhoc + 1e-4) ≤ 1 - v)
    (h3 : (2 * δ ^ 2 + δ') * Real.log 2 + R / p < cD * v / 2)
    (h2 : δ' * 0.7 < cD * 0.2328 / 2)
    (hδ'η : δ' < 0.095 * η)
    (hηρ : 1.23 * δ < 1.5849e-4 * η) :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s:ℝ) / q →
      (s:ℝ) / q ≤ 1.94 → η * q ≤ (s:ℝ) - q →
      ∀ L P, Rdelta δ s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q)) := by
  have hδsq : δ ^ 2 ≤ 1e-10 := by
    rw [sq]
    calc δ * δ ≤ 1e-5 * 1e-5 := mul_le_mul hδ5 hδ5 hδ0.le (by norm_num)
      _ = 1e-10 := by norm_num
  have hδsq0 : 0 ≤ δ ^ 2 := sq_nonneg δ
  exact K_core_paramG 1.23 3.5 (2 * δ ^ 2) η δ δ' cD v R p (hgt hBug cD hcD0 hcD1) hδ0
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hδ'c hcD0 hcDη hp2 hbp hrcp
    hv h3 h2 hδ'η hηρ

/-! ## The constants of §14.1 of the manuscript (version 2) -/

/-- `δ = 0.3𝔅 = 2.8055×10^{−7}` of §14.1 of the manuscript (version 2; a value independent of `α` for `α ≥ 0.500701`, obtained by rounding `0.3𝔅 = 2.80551×10^{−7}` down). -/
noncomputable def deltaE : ℝ := 2.8055e-7

/-- `δ' = 5δ/2` of §14.1 of the manuscript (version 2). -/
noncomputable def deltaE' : ℝ := 2.5 * deltaE

set_option maxHeartbeats 1000000 in
/-- The core of Proposition 14.1 (the constants of §14.1 of the manuscript, version 2): `c_D = 9×10^{−4}`, `p = 312`, `ρ♯ = ρ_c + 10^{−4}`, `δ = 2.8055×10^{−7}`, `δ' = 2.5δ`.
It holds for `η ≥ 0.0022` (`s − q ≥ ηq`). -/
theorem K_core_explicit (hBug : BugeaudHyp) (η : ℝ) (hη : 0.0022 ≤ η) :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s:ℝ) / q →
      (s:ℝ) / q ≤ 1.94 → η * q ≤ (s:ℝ) - q →
      ∀ L P, Rdelta deltaE s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(deltaE' * q)) := by
  have hl2 := Real.log_two_lt_d9
  have hθ := X_theta_phi312
  refine K_core_param hBug η deltaE deltaE' 9e-4 (0.0066 * 0.2328) 1.6e-5 312
    (by unfold deltaE; norm_num) (by unfold deltaE; norm_num) (by unfold deltaE' deltaE; norm_num)
    (by unfold deltaE' deltaE; norm_num) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) X_bp312 X_rc_pow312 ?_ ?_ (by unfold deltaE' deltaE; norm_num)
    (by unfold deltaE' deltaE; linarith) (by unfold deltaE; linarith)
  · exact hθ
  · have hpos : (0:ℝ) ≤ (2 * deltaE ^ 2 + deltaE') := by unfold deltaE' deltaE; norm_num
    have := mul_le_mul_of_nonneg_left hl2.le hpos
    unfold deltaE' deltaE at this ⊢
    push_cast
    norm_num at this ⊢
    linarith

/-- For `s = ⌊αK⌋ + 1` and `q = K − s`: `s − q ≥ (β_α − 1)q` (`β_α = α/(1 − α)`; from `s > αK`). -/
lemma X_sq_eta (α : ℝ) (hα1 : α < 1) (K : ℕ) (hsK : sOf α K ≤ K) :
    (2 * α - 1) / (1 - α) * ((K - sOf α K : ℕ) : ℝ) ≤ (sOf α K : ℝ) - ((K - sOf α K : ℕ) : ℝ) := by
  rw [Nat.cast_sub hsK]
  have hs : α * K < sOf α K := by
    unfold sOf; push_cast; exact Nat.lt_floor_add_one _
  have h1 : 0 < 1 - α := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ h1]
  nlinarith

/-- Proposition 14.1 (the constants of §14.1 of the manuscript, version 2): for `α ∈ [0.5006, 0.659]` and all sufficiently large `K`, `A_k ≤ 2^{−δ'q}` (`δ' = 2.5δ`)
for every slice of `R_δ` (`δ = 2.8055×10^{−7}`) and every shell. The condition `α ≥ 0.5006` is needed for `β_α − 1 ≥ 0.0022`. -/
theorem all_shells_explicit (hBug : BugeaudHyp) (α : ℝ) (hα : 0.5006 ≤ α) (hα' : α ≤ 0.659) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      ∀ L P, Rdelta deltaE (sOf α K) (K - sOf α K) L P → ∀ k ≤ L,
        Ak (K - sOf α K) (sOf α K) L P k ≤ (2:ℝ) ^ (-(deltaE' * (K - sOf α K : ℕ))) := by
  have hη : 0.0022 ≤ (2 * α - 1) / (1 - α) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨q0, hcore⟩ := K_core_explicit hBug _ hη
  obtain ⟨K0, hK0⟩ := sOf_ratio α (by linarith) hα' (max q0 1)
  refine ⟨K0, fun K hK L P hR k hk => ?_⟩
  obtain ⟨hq, hr1, hr2⟩ := hK0 K hK
  have hq1 : 1 ≤ K - sOf α K := le_trans (le_max_right _ _) hq
  refine hcore (sOf α K) (K - sOf α K) (le_trans (le_max_left _ _) hq) hr1 hr2 ?_ L P hR k hk
  exact X_sq_eta α (by linarith) K (by omega)

end Collatz.M1
