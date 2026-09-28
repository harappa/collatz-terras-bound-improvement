import CollatzProof.M1.S4
import CollatzProof.M1.S5
import CollatzProof.M1.S6
import CollatzProof.M1.S7
import CollatzProof.M1.S9
import CollatzProof.M1.S10
import CollatzProof.M1.S11
import CollatzProof.M1.S13
import CollatzProof.M1.K_Terms

/-!
# §14: Assembly and the main theorem (Theorem 1.1 of the paper, range version, qualitative form)

Assemble Proposition 14.1 (`A_k ≤ 2^{−δ'q}` on every shell) from the results of §6–§13, and derive the main theorem via Theorem B and Corollary A.

Outline of the assembly: `K_core` chooses the constants for `η = 2α − 1` by a qualitative rule (the qualitative version of the rule of manuscript §14.1),
and closes the outer shells (`k ≥ k₁`) by Proposition 9.2, and shell 0 and the inner shells by Lemmas 7.4, 7.5, Proposition 10.2 and the estimates of the 2nd–4th terms (`K_Terms.lean`).
The upper bound on `S_p^*` is obtained by passing the lattice condition of Proposition 13.2 (`hgt`) to Proposition 11.3 and related results (`Sstar_bound`) (`LatticeCond` is not unfolded).
-/

namespace Collatz.M1

open Finset Filter Topology

/-- The form of the conclusion of Proposition 13.2 (the supply of the lattice condition): for all sufficiently large `q` (the threshold does not depend on `L`, `s`), if `1 < s/q ≤ 1.94` and
`0 ≤ h_L ≤ 10^{−8}q`, then `LatticeCond q L ⌊c_D q⌋ (q2^D(q2^{h_L} + 1))`. Version 2 supplies it from Theorem 2 of Bugeaud (2002)
for `c_D ≤ 9×10^{−4}` (`hgt`, Proposition 13.2), version 3 from Theorem 1 for `c_D ≤ 9×10^{−3}` (`hgt_thm1`, Proposition 13.2B; Proposition 15.5 of the paper). -/
def HgtSupply (cD : ℝ) : Prop :=
  ∃ q0 : ℕ, ∀ s q L : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 → 0 ≤ hL s L →
    hL s L ≤ 1e-8 * q →
    LatticeCond q L ⌊cD * q⌋₊ (q * 2 ^ ⌊cD * q⌋₊ * (q * (2:ℝ) ^ hL s L + 1))

set_option maxHeartbeats 2000000 in
/-- Core of Proposition 14.1 (in terms of `q`): for `η > 0` there is `δ > 0` (with `δ' = 3δ`) such that, if `q` is sufficiently large,
`1 < s/q ≤ 1.94` and `s − q ≥ ηq`, then `A_k ≤ 2^{−δ'q}` for every slice of `R_δ` and every shell.
The constants are the qualitative version of the rule of manuscript §14.1: `ρ♯ = ρ_c + 1/10`, `Θ_* = Θ_{1/2}(ρ♯)`, `c_D = min(9×10^{−4}, η/2)`,
`p` is an integer with `r_c^p ≤ c_D w/4` and `((1+r_c)/2)^p ≤ 1/4` (where `w = ρ♯(1 − ρ♯)`),
`δ = min(10^{−5}, η/100, c_D w/(20p))`. -/
theorem K_coreG (hH : ∀ cD : ℝ, 0 < cD → cD ≤ 9e-4 → HgtSupply cD) (η : ℝ) (hη : 0 < η) :
    ∃ δ δ' : ℝ, 0 < δ ∧ δ ≤ 1e-3 ∧ 2 * δ < δ' ∧ ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s:ℝ) / q →
      (s:ℝ) / q ≤ 1.94 → η * q ≤ (s:ℝ) - q →
      ∀ L P, Rdelta δ s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q)) := by
  obtain ⟨hrc1, hrc2⟩ := rhoc_bounds
  obtain ⟨hr1, hr2⟩ := rc_bounds
  obtain ⟨hcc1, -⟩ := cc_bounds
  have hlog2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- ρ♯ = ρ_c + 1/10, w = ρ♯(1 − ρ♯), Θ_* = Θ_{1/2}(ρ♯) = 1 − w, l = log₂(1/Θ_*)
  obtain ⟨ρs, hρs⟩ : ∃ x : ℝ, x = rhoc + 1/10 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ x : ℝ, x = ρs * (1 - ρs) := ⟨_, rfl⟩
  have hw1 : 0.19 ≤ w := by
    rw [hw, hρs]
    nlinarith only [hrc1, hrc2, mul_nonneg (sub_nonneg.2 hrc1.le) (sub_nonneg.2 hrc2.le)]
  have hw2 : w ≤ 1/4 := by rw [hw]; nlinarith only [sq_nonneg (ρs - 1/2)]
  have hρs1 : rhoc + 1/10 ≤ 1 := by linarith
  obtain ⟨Θs, hΘs⟩ : ∃ x : ℝ, x = Theta (1/2) ρs := ⟨_, rfl⟩
  have hΘs_eq : Θs = 1 - w := by rw [hΘs, hw, Theta]; ring
  have hΘs0 : 0 < Θs := by linarith
  have hΘs1 : Θs < 1 := by linarith
  have hΘs34 : 3/4 ≤ Θs := by linarith
  obtain ⟨l, hl⟩ : ∃ x : ℝ, x = Real.logb 2 (1 / Θs) := ⟨_, rfl⟩
  have hl19 : 0.19 ≤ l := by
    rw [hl]; linarith [K_logb_ge Θs w hΘs_eq (by linarith) (by linarith)]
  have hl0 : 0 < l := by linarith
  -- c_D
  obtain ⟨cD, hcD⟩ : ∃ x : ℝ, x = min 9e-4 (η / 2) := ⟨_, rfl⟩
  have hcD0 : 0 < cD := by rw [hcD]; exact lt_min (by norm_num) (by linarith)
  have hcD1 : cD ≤ 9e-4 := by rw [hcD]; exact min_le_left _ _
  have hcD2 : cD ≤ η / 2 := by rw [hcD]; exact min_le_right _ _
  -- the Hölder exponent p
  obtain ⟨p, hp2, hrcp, hbp⟩ : ∃ p : ℕ, 2 ≤ p ∧ rc ^ p ≤ cD * w / 4 ∧ ((1 + rc) / 2) ^ p ≤ 1/4 := by
    obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one (show 0 < cD * w / 4 by positivity)
      (show rc < 1 by linarith)
    obtain ⟨n2, hn2⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1/4 by norm_num)
      (show (1 + rc) / 2 < 1 by linarith)
    refine ⟨max 2 (max n1 n2), le_max_left _ _, ?_, ?_⟩
    · exact (pow_le_pow_of_le_one (by linarith) (by linarith)
        ((le_max_left n1 n2).trans (le_max_right _ _))).trans hn1.le
    · exact (pow_le_pow_of_le_one (by linarith) (by linarith)
        ((le_max_right n1 n2).trans (le_max_right _ _))).trans hn2.le
  have hp0 : (0:ℝ) < p := by positivity
  have hp2' : (2:ℝ) ≤ p := by exact_mod_cast hp2
  obtain ⟨hφ1, hφ2⟩ := K_phiP p hp2
  have hφ1' : phiP p ≤ 1 := by linarith [show (0:ℝ) ≤ 1 / (2 * p) by positivity]
  obtain ⟨Θφ, hΘφ⟩ : ∃ x : ℝ, x = Theta (phiP p) ρs := ⟨_, rfl⟩
  have hΘφ34 : 3/4 ≤ Θφ := hΘφ ▸ K_theta_ge _ _ hφ1 hφ1'
  have hΘφ_le : Θφ ≤ 1 - w / p := by
    have e : Θφ = 1 - 2 * (1 - phiP p) * w := by rw [hΘφ, hw, Theta]; ring
    have h1 : 1 / (2 * p) ≤ 1 - phiP p := by linarith
    have e2 : w / p = 2 * (1 / (2 * p)) * w := by field_simp
    have := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 2 * w by linarith)
    rw [e, e2]; linarith only [this]
  have hΘφ1 : Θφ ≤ 1 := by linarith [show (0:ℝ) ≤ w / p by positivity]
  -- δ and δ' = 3δ
  obtain ⟨δ, hδ⟩ : ∃ x : ℝ, x = min 1e-5 (min (η / 100) (cD * w / (20 * p))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]; exact lt_min (by norm_num) (lt_min (by linarith) (by positivity))
  have hδ5 : δ ≤ 1e-5 := by rw [hδ]; exact min_le_left _ _
  have hδη : δ ≤ η / 100 := by rw [hδ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδp : δ ≤ cD * w / (20 * p) := by
    rw [hδ]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hδ1e3 : δ ≤ 1e-3 := by linarith
  refine ⟨δ, 3 * δ, hδ0, hδ1e3, by linarith, ?_⟩
  have hδ'0 : 0 < 3 * δ := by linarith
  have hδ'c : 3 * δ < cc / 2 := by linarith
  have h20p : 20 * p * δ ≤ cD * w := by
    rw [le_div_iff₀ (by positivity)] at hδp; linarith
  have hcw : 0 < cD * w := by positivity
  -- rates
  have hu2 : Θs ^ (cD / 2) * (2:ℝ) ^ (3 * δ) < 1 := by
    refine K_rate2 Θs w cD (3 * δ) hΘs_eq (by linarith) hcD0.le ?_
    have : 3 * δ * Real.log 2 ≤ 3 * δ * 0.7 := mul_le_mul_of_nonneg_left hlog2.le (by linarith)
    have h2δ := mul_le_mul_of_nonneg_right hp2' hδ0.le
    linarith only [this, h20p, h2δ, hδ0]
  have hu3 : (2:ℝ) ^ (2 * δ ^ 2) * (1 + rc ^ p) ^ (1 / (p:ℝ)) * Θφ ^ (cD / 2) *
      (2:ℝ) ^ (3 * δ) < 1 := by
    refine K_rate3 p (by omega) Θφ w cD δ (3 * δ) (by linarith) hΘφ_le hrcp hcD0.le ?_
    rw [lt_div_iff₀ (by positivity)]
    have hδsq : 2 * δ ^ 2 ≤ δ := by
      nlinarith only [hδ0, hδ5, mul_le_mul_of_nonneg_left hδ5 hδ0.le]
    have a1 : (2 * δ ^ 2 + 3 * δ) * Real.log 2 ≤ (4 * δ) * 0.7 :=
      mul_le_mul (by linarith) hlog2.le hlog20.le (by linarith)
    have a2 : (2 * δ ^ 2 + 3 * δ) * Real.log 2 * (4 * p) ≤ (4 * δ) * 0.7 * (4 * p) :=
      mul_le_mul_of_nonneg_right a1 (by positivity)
    linarith only [a2, h20p, mul_pos hδ0 hp0]
  have hc4 : 0 < 1 - 2 * (3 * δ) - 2 * (3 * δ) / l := by
    have : 2 * (3 * δ) / l ≤ 2 * (3 * δ) / 0.19 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hl19
    have h2 : 2 * (3 * δ) / (0.19:ℝ) ≤ 2 * (3 * 1e-5) / 0.19 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have h3 : 2 * (3 * (1e-5:ℝ)) / 0.19 < 0.01 := by norm_num
    linarith only [this, h2, h3, hδ5]
  -- thresholds of the components
  obtain ⟨qj, hj⟩ := choose_j0 δ (3 * δ) hδ0 hδ1e3 hδ'0 hδ'c
  obtain ⟨qo, ho⟩ := outer_shells δ (3 * δ) Θs hδ0 hδ1e3 hδ'0 hΘs0 hΘs1
  obtain ⟨qh, hh⟩ := hH cD hcD0 hcD1
  -- the inequalities that eventually hold
  have ev := ((((((((eventually_ge_atTop (max (max 20 qj) (max qo qh))).and
    (K_ev_lin (2 / cD) 1 one_pos)).and
    (K_ev_lin (2 / η) 1 one_pos)).and
    (K_ev_lin 0.758 (0.158 * η - 1.23 * δ) (by linarith))).and
    (K_ev_log (3 + 0.19) 2 (0.095 * η - 3 * δ) (by linarith))).and
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
  -- ρ̄ is closer to ρ_c than ρ♯ is (Lemma 6.4)
  have hΘall : ∀ γ : ℝ, γ ≤ 1 → ∀ L P, Rdelta δ s q L P →
      Theta γ (rhoBar q s L P) ≤ Theta γ ρs := by
    intro γ hγ L P hR
    obtain ⟨hrb, -⟩ := rhoBar_close δ s q L P hδ0 hδ1e3 hqs hR
    have hε : (1.23 * δ * q + aa) / (lam * (s - q - 1)) ≤ 1 / 10 := by
      have hlam := lam_bounds
      have hpos : 0 < lam * ((s:ℝ) - q - 1) := by
        apply mul_pos (by linarith); linarith
      rw [div_le_iff₀ hpos]
      have ha : aa < 0.6 := by unfold aa; linarith
      have hsq' : η * q - 1 ≤ (s:ℝ) - q - 1 := by linarith
      have h158 : 1.58 * (η * q - 1) ≤ lam * ((s:ℝ) - q - 1) :=
        mul_le_mul (by linarith) hsq' (by linarith) (by linarith)
      have : 0.758 ≤ (0.158 * η - 1.23 * δ) * q := hErho
      linarith
    rw [hρs]
    exact Theta_le_of_close γ _ (1/10) hγ (by norm_num) hρs1 (hrb.trans hε)
  have hYout := K_Yout_cond q s (3 * δ) Θs l η hl hl19 hδ'0.le hs1 hs2q hηq hqs hEY
  intro L P hR k hk
  obtain ⟨hL0, hLup, -, -, -, hTne, -⟩ := id hR
  have hLsmall : hL s L ≤ 1e-8 * q := by
    have hδsq : δ ^ 2 ≤ 1e-10 := by
      rw [sq]
      calc δ * δ ≤ 1e-5 * 1e-5 := mul_le_mul hδ5 hδ5 hδ0.le (by norm_num)
        _ = 1e-10 := by norm_num
    have : 3.5 * δ ^ 2 * q ≤ 1e-8 * q := mul_le_mul_of_nonneg_right (by linarith) hqpos.le
    linarith
  -- outer shells (Proposition 9.2)
  by_cases hk1 : k1out (3 * δ) Θs s q ≤ k
  · refine ho s q hqo hsq1 hsq2 (fun L P hR => ?_) hYout L P hR k hk1 hk
    have := hΘall (1/2) (by norm_num) L P hR
    rwa [← hΘs] at this
  -- shell 0 and the inner shells (Lemma 7.4, Proposition 10.2)
  push Not at hk1
  obtain ⟨j0, hj0q, hvar, hE⟩ := hj s q L P hqj hsq1 hsq2 hR
  rcases (K_Wsum_nonneg q (Eset q (hL s L))).eq_or_lt with hW0 | hWpos
  · rw [K_Ak_zero q s L P k hW0.symm]; positivity
  obtain ⟨-, hsP⟩ := rhoBar_close δ s q L P hδ0 hδ1e3 hqs hR
  have hD2 : 2 ≤ ⌊cD * q⌋₊ := by
    apply Nat.le_floor
    have := hED; rw [one_mul, div_le_iff₀ hcD0] at this
    push_cast; linarith
  have hDt : ⌊cD * q⌋₊ ≤ s - P - 1 := by
    have h1 : (⌊cD * q⌋₊ : ℝ) ≤ cD * q := Nat.floor_le (by positivity)
    have h2 : (⌊cD * q⌋₊ : ℝ) ≤ ((s - q : ℕ) : ℝ) := by
      have h3 : cD * q ≤ η / 2 * q := mul_le_mul_of_nonneg_right hcD2 hqpos.le
      rw [Nat.cast_sub (by omega)]; linarith
    have : ⌊cD * q⌋₊ ≤ s - q := by exact_mod_cast h2
    omega
  have hpow1 : (2:ℝ) ^ (-(3 * δ * q)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.2 (by positivity))
  have hvar2 : varpi q s L j0 ≤ (2:ℝ) ^ (-(3 * δ * q)) / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one] at hvar; exact hvar
  have hvar_half : varpi q s L j0 ≤ 1 / 2 := by linarith
  have hvar0 := K_varpi_nonneg q s L j0
  have hhold := holder δ s q L P j0 ⌊cD * q⌋₊ k (p:ℝ) hδ0 hδ1e3 hsq1 hsq2 h20 hR hD2 hp2' hk
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
  have hT2 := K_term2 q s L P cD Θs (3 * δ) hΘs34 hΘs1.le hD2 hDt hL0 hTne
    (by rw [hΘs]; exact hΘall _ (by norm_num) L P hR) hsP2 hE2
  have hSS := Sstar_bound s q L j0 ⌊cD * q⌋₊ p (q * (2:ℝ) ^ hL s L) hp2' (by omega) h20
    (by positivity) hL0 hE hvar_half (by omega) (hh s q L hqh hsq1 hsq2 hL0 hLsmall)
  have hT3 := K_term3 q s L P j0 p cD Θφ δ (3 * δ) hp2 hΘφ34 hΘφ1 hD2 hDt hL0 hLup hTne hφ1 hφ1'
    (by rw [hΘφ]; exact hΘall _ hφ1' L P hR) hsP2 hj0q hbp hSS hE3
  have hT4 := K_term4 q s k (3 * δ) Θs l hl hl0 hδ'0.le hs1 hs2q hk1 hE4
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
  have hpos2 : (0:ℝ) < (2:ℝ) ^ (-(3 * δ * q)) := by positivity
  linarith only [hsplit, hdeep, hvar2, hT2, hT3, hT4, hpos2]

/-- The core of Proposition 14.1 (from Theorem 2 of Bugeaud (2002), via `hgt`): the specialization of `K_coreG`, which takes the supply of the lattice condition as an argument. -/
theorem K_core (hBug : BugeaudHyp) (η : ℝ) (hη : 0 < η) :
    ∃ δ δ' : ℝ, 0 < δ ∧ δ ≤ 1e-3 ∧ 2 * δ < δ' ∧ ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s:ℝ) / q →
      (s:ℝ) / q ≤ 1.94 → η * q ≤ (s:ℝ) - q →
      ∀ L P, Rdelta δ s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q)) :=
  K_coreG (fun cD h0 h1 => hgt hBug cD h0 h1) η hη

/-- Proposition 14.1 (with the supply of the lattice condition as an argument): for `α ∈ (1/2, 0.659]` there are `0 < δ ≤ 10^{−3}` and `δ' > 2δ` such that, for all sufficiently large `K`,
`A_k ≤ 2^{−δ'q}` for every slice of `R_δ` and every shell `0 ≤ k ≤ L`. -/
theorem all_shellsG (hH : ∀ cD : ℝ, 0 < cD → cD ≤ 9e-4 → HgtSupply cD) (α : ℝ) (hα : 1 / 2 < α)
    (hα' : α ≤ 0.659) :
    ∃ δ δ' : ℝ, 0 < δ ∧ δ ≤ 1e-3 ∧ 2 * δ < δ' ∧ ∃ K0 : ℕ, ∀ K ≥ K0,
      ∀ L P, Rdelta δ (sOf α K) (K - sOf α K) L P → ∀ k ≤ L,
        Ak (K - sOf α K) (sOf α K) L P k ≤ (2:ℝ) ^ (-(δ' * (K - sOf α K : ℕ))) := by
  obtain ⟨δ, δ', hδ, hδ1, hδ', q0, hcore⟩ := K_coreG hH (2 * α - 1) (by linarith)
  refine ⟨δ, δ', hδ, hδ1, hδ', ?_⟩
  obtain ⟨K0, hK0⟩ := sOf_ratio α hα hα' (max q0 1)
  refine ⟨K0, fun K hK L P hR k hk => ?_⟩
  obtain ⟨hq, hr1, hr2⟩ := hK0 K hK
  refine hcore (sOf α K) (K - sOf α K) (le_trans (le_max_left _ _) hq) hr1 hr2 ?_ L P hR k hk
  -- `s − q ≥ (2α − 1)q`: from `s > αK`
  have hq1 : 1 ≤ K - sOf α K := le_trans (le_max_right _ _) hq
  have hsK : sOf α K ≤ K := by omega
  rw [Nat.cast_sub hsK]
  have hs : α * K < sOf α K := by
    unfold sOf; push_cast; exact Nat.lt_floor_add_one _
  have hK0' : (0:ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 * α - 1 by linarith) hK0']

/-- Proposition 14.1 (from Theorem 2 of Bugeaud (2002)). -/
theorem all_shells (hBug : BugeaudHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
    ∃ δ δ' : ℝ, 0 < δ ∧ δ ≤ 1e-3 ∧ 2 * δ < δ' ∧ ∃ K0 : ℕ, ∀ K ≥ K0,
      ∀ L P, Rdelta δ (sOf α K) (K - sOf α K) L P → ∀ k ≤ L,
        Ak (K - sOf α K) (sOf α K) L P k ≤ (2:ℝ) ^ (-(δ' * (K - sOf α K : ℕ))) :=
  all_shellsG (fun cD h0 h1 => hgt hBug cD h0 h1) α hα hα'

/-- The main theorem (qualitative form), with the supply of the lattice condition as an argument. -/
theorem m1_mainG (hH : ∀ cD : ℝ, 0 < cD → cD ≤ 9e-4 → HgtSupply cD) (α : ℝ) (hα : 1 / 2 < α)
    (hα' : α ≤ 0.659) :
    ∃ ε > 0, ∃ K0 : ℕ, ∀ K ≥ K0,
      (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨δ, δ', hδ, hδ1, hδ', K0, hshell⟩ := all_shellsG hH α hα hα'
  obtain ⟨q0, hB⟩ := thmB δ δ' hδ hδ1 hδ'
  obtain ⟨K1, hK1⟩ := sOf_ratio α hα hα' q0
  have hWF : ∃ K2 : ℕ, ∀ K ≥ K2, WF δ (sOf α K) (K - sOf α K) := by
    refine ⟨max K0 K1, fun K hK => ?_⟩
    obtain ⟨hq, hr1, hr2⟩ := hK1 K (le_trans (le_max_right _ _) hK)
    exact hB (sOf α K) (K - sOf α K) hq hr1 hr2
      (fun L P hR k hk => hshell K (le_trans (le_max_left _ _) hK) L P hR k hk)
  have hc : cc < 1 := by have := cc_bounds; linarith
  set m := min (1.70 * δ ^ 2 * (1 - α)) ((1 - cc) * (2 * α - 1) / 2) with hm
  have hm0 : 0 < m := by
    apply lt_min
    · have : 0 < 1 - α := by linarith
      positivity
    · have : 0 < 1 - cc := by linarith
      have : 0 < 2 * α - 1 := by linarith
      positivity
  refine ⟨m / 2, by positivity, ?_⟩
  exact corA α δ hα hα' hδ hδ1 hWF (m / 2) (by linarith)

/-- **Main theorem (Theorem 1.1 of the paper, range version, qualitative form)**: assuming Theorem 2 of Bugeaud (2002), for every `α ∈ (1/2, 0.659]`
there are `ε > 0` and `K₀` such that `#(𝒩_K ∩ [1, 2^{αK}]) ≤ 2^{(α(1−c) − ε)K}` for all `K ≥ K₀`.
In particular `F(α) ≤ α(1−c) − ε` (strictly below the Terras-type upper bound `α(1−c)`). -/
theorem m1_main (hBug : BugeaudHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
    ∃ ε > 0, ∃ K0 : ℕ, ∀ K ≥ K0,
      (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) :=
  m1_mainG (fun cD h0 h1 => hgt hBug cD h0 h1) α hα hα'

end Collatz.M1
