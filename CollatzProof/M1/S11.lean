import CollatzProof.M1.Phase
import CollatzProof.M1.I_Phys
import CollatzProof.M1.I_Mult
import CollatzProof.M1.I_Corr

/-! # §11–§12: reduction to the physical side, multiplicity, the majorant by Bhattacharyya coefficients, and the moment bound

The combined form of Propositions 11.3 and 11.5, Corollary 12.2 and Proposition 12.4.

Components of the proof (auxiliary files, prefix `I_`):
- `I_Kernel.lean`: `e(x)`, orthogonality, the Dirichlet kernel, the kernel sum `≤ q+2`, re-indexing sums of periodic functions.
- `I_Four.lean`: expansion of `|Ê|²`, `r^{deep} = r_E − r^{sh}`, Parseval, the bound on the average over `μ` (second half of Lemma 11.2).
- `I_Phys.lean`: the expansions of Lemmas 11.1 and 11.2, step 2 of Proposition 11.3, the kernel bound.
- `I_Mult.lean`: Proposition 11.5 (multiplicity `≤ 25`, packing).
- `I_BC.lean`, `I_Corr.lean`: Lemmas 12.1 and 12.3, Proposition 12.4, the core of Corollary 12.2. -/

namespace Collatz.M1

open Finset

/-- Weighted Jensen: if `w, x ≥ 0`, `p ≥ 1` and `Σw ≤ Ω`, then `(Σ wx)^p ≤ Ω^{p−1} Σ w x^p`. -/
lemma I_jensen {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) (p : ℝ) (hp : 1 ≤ p) (Ω : ℝ) (hΩ : ∑ i ∈ s, w i ≤ Ω) :
    (∑ i ∈ s, w i * x i) ^ p ≤ Ω ^ (p - 1) * ∑ i ∈ s, w i * x i ^ p := by
  set S := ∑ i ∈ s, w i with hS
  have hS0 : 0 ≤ S := sum_nonneg hw
  have hΩ0 : 0 ≤ Ω := le_trans hS0 hΩ
  have hR0 : 0 ≤ ∑ i ∈ s, w i * x i ^ p :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hx i hi) _)
  rcases hS0.lt_or_eq with hSpos | hSz
  · have hj := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / S) x
      (fun i hi => div_nonneg (hw i hi) hS0) (by rw [← sum_div, ← hS, div_self hSpos.ne']) hx hp
    have e1 : ∑ i ∈ s, w i * x i = S * ∑ i ∈ s, w i / S * x i := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; field_simp
    have e2 : ∑ i ∈ s, w i / S * x i ^ p = S⁻¹ * ∑ i ∈ s, w i * x i ^ p := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; field_simp
    have hm0 : 0 ≤ ∑ i ∈ s, w i / S * x i :=
      sum_nonneg fun i hi => mul_nonneg (div_nonneg (hw i hi) hS0) (hx i hi)
    rw [e1, Real.mul_rpow hS0 hm0]
    calc S ^ p * (∑ i ∈ s, w i / S * x i) ^ p ≤ S ^ p * ∑ i ∈ s, w i / S * x i ^ p :=
          mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hS0 _)
      _ = S ^ (p - 1) * ∑ i ∈ s, w i * x i ^ p := by
          rw [e2, Real.rpow_sub_one hSpos.ne']; field_simp
      _ ≤ Ω ^ (p - 1) * ∑ i ∈ s, w i * x i ^ p :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hS0 hΩ (by linarith)) hR0
  · have hw0 : ∀ i ∈ s, w i = 0 := (sum_eq_zero_iff_of_nonneg hw).mp hSz.symm
    have : ∑ i ∈ s, w i * x i = 0 := sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul]
    rw [this, Real.zero_rpow (by linarith)]
    exact mul_nonneg (Real.rpow_nonneg hΩ0 _) hR0

/-- `(x + y)^p ≤ 2^{p−1}(x^p + y^p)` (`x, y ≥ 0`, `p ≥ 1`). -/
lemma I_add_rpow_le (x y p : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 1 ≤ p) :
    (x + y) ^ p ≤ 2 ^ (p - 1) * (x ^ p + y ^ p) := by
  have hc := (convexOn_rpow hp).2 (x := x) (y := y) (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hc
  have e : x + y = 2 * (1 / 2 * x + 1 / 2 * y) := by ring
  rw [e, Real.mul_rpow (by norm_num) (by positivity)]
  calc (2 : ℝ) ^ p * (1 / 2 * x + 1 / 2 * y) ^ p ≤ 2 ^ p * (1 / 2 * x ^ p + 1 / 2 * y ^ p) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2 ^ (p - 1) * (x ^ p + y ^ p) := by rw [Real.rpow_sub_one (by norm_num)]; ring

/-- Corollary 12.2 and Proposition 12.4 combined: `Σ_v ϱ_E(v)^p ≤ 2^{p−1}R_E^p((1+r_c^p)^q + 2^q((1+r_c)/2)^{p(q−j₀)})`,
`R_E = 2^{t*h_L+1.1}q(q+1)`. -/
lemma I_rho_moment (s q L j0 : ℕ) (p : ℝ) (hp : 1 ≤ p) (hq : 20 ≤ q) (hL0 : 0 ≤ hL s L) (hj0 : j0 ≤ q) :
    ∑ v ∈ range (2 ^ q), rhoE q s L j0 v ^ p ≤
      2 ^ (p - 1) * ((2 : ℝ) ^ (tstar * hL s L + 1.1) * q * (q + 1)) ^ p *
        ((1 + rc ^ p) ^ q + 2 ^ q * ((1 + rc) / 2) ^ (p * (q - j0))) := by
  set E := Eset q (hL s L) with hEdef
  have hq1 : 1 ≤ q := by omega
  have hElow := E_lower q hq (hL s L) hL0
  rw [← hEdef] at hElow
  have hEpos : (0 : ℝ) < E.card := lt_of_lt_of_le (by positivity) hElow
  have hEsub : E ⊆ range (2 ^ q) := by
    intro z hz; rw [hEdef] at hz; simp only [Eset, Finset.mem_filter] at hz; exact hz.1
  have hf : 0 < ff := by unfold ff; positivity
  set C : ℝ := (2 : ℝ) ^ (tstar * hL s L) * (2 * ff) ^ q with hC
  have hC0 : 0 ≤ C := by positivity
  set K : ℝ := Real.sqrt C with hK
  have hKsq : K ^ 2 = C := Real.sq_sqrt hC0
  have hw : ∀ z ∈ E, 1 ≤ K * I_gw I_sa I_sb q z := fun z hz => I_E_weight_sqrt q hq1 (hL s L) z hz
  set g : ℝ := ((1 + rc) / 2) ^ (q - j0) with hg
  have hg0 : 0 ≤ g := by have := I_rc_nonneg; positivity
  set R : ℝ := (2 : ℝ) ^ (tstar * hL s L + 1.1) * q * (q + 1) with hR
  have hR0 : 0 ≤ R := by positivity
  -- `C/|E| ≤ R`
  have hCE : C / E.card ≤ R := by
    have h2f : 2 * ff = (2 : ℝ) ^ (1 - cc) := by
      unfold ff; rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]; field_simp
    have hCq : (2 * ff) ^ q = (2 : ℝ) ^ ((1 - cc) * q) := by
      rw [h2f, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have hqq : (0 : ℝ) < q * (q + 1) := by positivity
    rw [div_le_iff₀ hEpos]
    calc C = (2 : ℝ) ^ (tstar * hL s L) * 2 ^ ((1 - cc) * q) := by rw [hC, hCq]
      _ = R * (2 ^ ((1 - cc) * q - 1.1) / (q * (q + 1))) := by
          rw [hR, Real.rpow_add (by norm_num), Real.rpow_sub (by norm_num)]; field_simp
      _ ≤ R * E.card := mul_le_mul_of_nonneg_left hElow hR0
  -- Bound at each `v`
  have hrho : ∀ v : ℕ, rhoE q s L j0 v ≤ R * (I_Phi I_sa I_sb q 1 v + g) := by
    intro v
    have h1 := I_rDeep_le q s L j0 hj0 v
    rw [← hEdef] at h1
    have h2 := I_rE_le q E hEsub K hw v
    have h3 := I_rSh_le q j0 hj0 E hEsub K hw v
    rw [hKsq] at h2 h3
    have hΦ0 : 0 ≤ I_Phi I_sa I_sb q 1 v := I_Phi_nonneg I_sa_nonneg I_sb_nonneg _ _ _
    unfold rhoE; rw [← hEdef]
    rw [div_le_iff₀ hEpos]
    calc ‖rDeep q s L j0 v‖ ≤ C * (I_Phi I_sa I_sb q 1 v + g) := by rw [mul_add]; linarith
      _ = C / E.card * (I_Phi I_sa I_sb q 1 v + g) * E.card := by field_simp
      _ ≤ R * (I_Phi I_sa I_sb q 1 v + g) * E.card := by
          apply mul_le_mul_of_nonneg_right _ hEpos.le
          exact mul_le_mul_of_nonneg_right hCE (by positivity)
  -- Raise to the power `p` and sum
  have hpt : ∀ v ∈ range (2 ^ q), rhoE q s L j0 v ^ p ≤
      2 ^ (p - 1) * R ^ p * (I_Phi I_sa I_sb q 1 v ^ p + g ^ p) := by
    intro v _
    have hΦ0 : 0 ≤ I_Phi I_sa I_sb q 1 v := I_Phi_nonneg I_sa_nonneg I_sb_nonneg _ _ _
    have hr0 : 0 ≤ rhoE q s L j0 v := div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
    calc rhoE q s L j0 v ^ p ≤ (R * (I_Phi I_sa I_sb q 1 v + g)) ^ p :=
          Real.rpow_le_rpow hr0 (hrho v) (by linarith)
      _ = R ^ p * (I_Phi I_sa I_sb q 1 v + g) ^ p := Real.mul_rpow hR0 (by positivity)
      _ ≤ R ^ p * (2 ^ (p - 1) * (I_Phi I_sa I_sb q 1 v ^ p + g ^ p)) :=
          mul_le_mul_of_nonneg_left (I_add_rpow_le _ _ p hΦ0 hg0 hp) (Real.rpow_nonneg hR0 _)
      _ = _ := by ring
  refine le_trans (sum_le_sum hpt) ?_
  rw [← mul_sum, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hmom := I_moment I_sa_nonneg I_sb_nonneg I_sq_add p hp q 1 (by norm_num)
  rw [I_two_sa_sb] at hmom
  have hgp : g ^ p = ((1 + rc) / 2) ^ (p * ((q : ℝ) - j0)) := by
    rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul (by have := I_rc_nonneg; positivity),
      Nat.cast_sub hj0, mul_comm]
  rw [hgp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  push_cast
  linarith

/-- Bound on `S_p^*(B)`: for `p ≥ 2`, `D ≥ 1`, `q ≥ 20`, `B ≥ 0`, `h_L ≥ 0`, `|E| ≤ 2^{q−1}`, `ϖ_{j₀} ≤ 1/2`,
under the lattice condition `λ₁(Λ_L) ≥ q2^D(B+1)`,
`S_p^*(B) ≤ (q+2)^{2(p−1)} 4^p · 25 · 2^{p−1} R_E^p ((1 + r_c^p)^q + 2^q((1+r_c)/2)^{p(q−j₀)})`, `R_E = 2^{t*h_L+1.1}q(q+1)`.

(Correction of the statement, 2026-09-25: the argument order of `LatticeCond` is `q L D H` (because of how the `variable`s of `DeepDefs.lean` are included).
The skeleton's `LatticeCond q D L (...)` had `L` and `D` swapped, so, in the sense of the manuscript's lattice `{(a, b) | a ≡ 3^L b (mod 2^{q+D})}`,
it was corrected to `LatticeCond q L D (...)`.) -/
theorem Sstar_bound (s q L j0 D : ℕ) (p B : ℝ) (hp : 2 ≤ p) (hD : 1 ≤ D) (hq : 20 ≤ q) (hB : 0 ≤ B)
    (hL0 : 0 ≤ hL s L) (hE : ((Eset q (hL s L)).card : ℝ) ≤ 2 ^ (q - 1)) (hvar : varpi q s L j0 ≤ 1 / 2)
    (hj0 : j0 ≤ q) (hlat : LatticeCond q L D (q * 2 ^ D * (B + 1))) :
    Sstar q s L j0 D p B ≤
      ((q : ℝ) + 2) ^ (2 * (p - 1)) * 4 ^ p * 25 * 2 ^ (p - 1) *
        ((2:ℝ) ^ (tstar * hL s L + 1.1) * q * (q + 1)) ^ p *
        ((1 + rc ^ p) ^ q + 2 ^ q * ((1 + rc) / 2) ^ (p * (q - j0))) := by
  set E := Eset q (hL s L) with hEdef
  have hq4 : 4 ≤ q := by omega
  have hq1 : 1 ≤ q := by omega
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hElow := E_lower q hq (hL s L) hL0
  have hEpos' : (0 : ℝ) < (Eset q (hL s L)).card := lt_of_lt_of_le (by positivity) hElow
  have hEpos : 0 < (Eset q (hL s L)).card := by exact_mod_cast hEpos'
  have h1v : 0 < 1 - varpi q s L j0 := by linarith
  set A : ℝ := 2 / (1 - varpi q s L j0) with hA
  have hA0 : 0 ≤ A := by positivity
  have hA4 : A ≤ 4 := by rw [hA, div_le_iff₀ h1v]; linarith
  have hmu : ∀ v : ℕ, ‖∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) * eC ((v : ℝ) * ξ / 2 ^ q)‖ ≤
      A * rhoE q s L j0 v := fun v => I_mu_sum_le q s L j0 hq1 hE hEpos hvar v
  have hrho0 : ∀ v, 0 ≤ rhoE q s L j0 v := fun v => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  set Ω : ℝ := ((q : ℝ) + 2) ^ 2 with hΩ
  have hΩ0 : 0 ≤ Ω := by positivity
  -- Weights `W_{h,j,v} = w(n_j)K(v, n_j)`
  set Wt : ℕ → ℕ → ℕ → ℝ := fun h j v =>
    I_kf (2 ^ q * I_nd (((h + 2 ^ D * j : ℕ) : ℝ) / 2 ^ (q + D))) *
      I_kf (2 ^ q * I_nd ((((h + 2 ^ D * j : ℕ) : ℝ) * 3 ^ L / 2 ^ D - v) / 2 ^ q) - B) with hWt
  have hWt0 : ∀ h j v, 0 ≤ Wt h j v := fun h j v => mul_nonneg (I_kf_nonneg _) (I_kf_nonneg _)
  -- Bound for each `h` (steps 2 and 3 of Proposition 11.3)
  have hstep : ∀ h ∈ Ico 1 (2 ^ D), (⨆ β : Set.Icc (-B) B, ‖muChar q s L j0 D h β‖ ^ p) ≤
      Ω ^ (p - 1) * ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q), Wt h j v * (A * rhoE q s L j0 v) ^ p := by
    intro h _
    have : Nonempty (Set.Icc (-B) B) := ⟨⟨0, by constructor <;> linarith⟩⟩
    apply ciSup_le
    rintro ⟨β, hβ⟩
    have hβ' : |β| ≤ B := abs_le.mpr ⟨hβ.1, hβ.2⟩
    have h1 := I_muChar_le q s L j0 D h β A hmu
    set ω : ℕ → ℕ → ℝ := fun j v => ‖I_psi q D h j‖ * ‖I_kk q (I_theta q D L h j β) v‖ with hω
    set x : ℕ → ℕ → ℝ := fun _ v => A * rhoE q s L j0 v with hx
    have hω0 : ∀ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q), 0 ≤ ω jv.1 jv.2 :=
      fun jv _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hx0 : ∀ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q), 0 ≤ x jv.1 jv.2 :=
      fun jv _ => mul_nonneg hA0 (hrho0 _)
    have hsumω : ∑ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q), ω jv.1 jv.2 ≤ Ω := by
      rw [sum_product' (f := ω)]
      calc ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q), ω j v =
            ∑ j ∈ range (2 ^ q), ‖I_psi q D h j‖ *
              ∑ v ∈ range (2 ^ q), ‖I_kk q (I_theta q D L h j β) v‖ := by
            apply sum_congr rfl; intro j _; rw [mul_sum]
        _ ≤ ∑ j ∈ range (2 ^ q), ‖I_psi q D h j‖ * ((q : ℝ) + 2) :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (I_kk_sum_le q hq4 _) (norm_nonneg _)
        _ = (∑ j ∈ range (2 ^ q), ‖I_psi q D h j‖) * ((q : ℝ) + 2) := by rw [sum_mul]
        _ ≤ ((q : ℝ) + 2) * ((q : ℝ) + 2) :=
            mul_le_mul_of_nonneg_right (I_psi_sum_le q D h hq4) (by positivity)
        _ = Ω := by rw [hΩ]; ring
    have hJ := I_jensen (range (2 ^ q) ×ˢ range (2 ^ q)) (fun jv => ω jv.1 jv.2) (fun jv => x jv.1 jv.2)
      hω0 hx0 p hp1 Ω hsumω
    have h1' : ‖muChar q s L j0 D h β‖ ≤
        ∑ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q), ω jv.1 jv.2 * x jv.1 jv.2 := by
      rw [sum_product' (f := fun j v => ω j v * x j v)]; exact h1
    have hWle : ∀ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q),
        ω jv.1 jv.2 * x jv.1 jv.2 ^ p ≤ Wt h jv.1 jv.2 * x jv.1 jv.2 ^ p := by
      intro jv hjv
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hx0 jv hjv) _)
      exact mul_le_mul (I_psi_le q D h jv.1) (I_kk_theta_le q D L h jv.1 β B hβ' jv.2)
        (norm_nonneg _) (I_kf_nonneg _)
    calc ‖muChar q s L j0 D h β‖ ^ p ≤
          (∑ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q), ω jv.1 jv.2 * x jv.1 jv.2) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) h1' hp0.le
      _ ≤ Ω ^ (p - 1) * ∑ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q), ω jv.1 jv.2 * x jv.1 jv.2 ^ p := hJ
      _ ≤ Ω ^ (p - 1) * ∑ jv ∈ range (2 ^ q) ×ˢ range (2 ^ q), Wt h jv.1 jv.2 * x jv.1 jv.2 ^ p :=
          mul_le_mul_of_nonneg_left (sum_le_sum hWle) (Real.rpow_nonneg hΩ0 _)
      _ = Ω ^ (p - 1) * ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q), Wt h j v * (A * rhoE q s L j0 v) ^ p := by
          rw [sum_product' (f := fun j v => Wt h j v * x j v ^ p)]
  -- Sum over `h` (step 4 of Proposition 11.3 and Proposition 11.5)
  have hmult : ∀ v ∈ range (2 ^ q), ∑ h ∈ Ico 1 (2 ^ D), ∑ j ∈ range (2 ^ q), Wt h j v ≤ 25 := by
    intro v _
    have := I_mult_le q D L B hB (by omega) (v : ℤ) hlat
    simpa [hWt] using this
  have hsum : ∑ h ∈ Ico 1 (2 ^ D), ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q),
      Wt h j v * (A * rhoE q s L j0 v) ^ p ≤ 25 * ∑ v ∈ range (2 ^ q), (A * rhoE q s L j0 v) ^ p := by
    have e : ∑ h ∈ Ico 1 (2 ^ D), ∑ j ∈ range (2 ^ q), ∑ v ∈ range (2 ^ q),
        Wt h j v * (A * rhoE q s L j0 v) ^ p =
        ∑ v ∈ range (2 ^ q), (∑ h ∈ Ico 1 (2 ^ D), ∑ j ∈ range (2 ^ q), Wt h j v) *
          (A * rhoE q s L j0 v) ^ p := by
      calc _ = ∑ h ∈ Ico 1 (2 ^ D), ∑ v ∈ range (2 ^ q), ∑ j ∈ range (2 ^ q),
            Wt h j v * (A * rhoE q s L j0 v) ^ p := by
            apply sum_congr rfl; intro h _; rw [sum_comm]
        _ = ∑ v ∈ range (2 ^ q), ∑ h ∈ Ico 1 (2 ^ D), ∑ j ∈ range (2 ^ q),
            Wt h j v * (A * rhoE q s L j0 v) ^ p := by rw [sum_comm]
        _ = _ := by
            apply sum_congr rfl; intro v _; rw [sum_mul]; apply sum_congr rfl; intro h _
            rw [sum_mul]
    rw [e, mul_sum]
    apply sum_le_sum; intro v hv
    exact mul_le_mul_of_nonneg_right (hmult v hv) (Real.rpow_nonneg (mul_nonneg hA0 (hrho0 v)) _)
  have hSstar : Sstar q s L j0 D p B ≤
      Ω ^ (p - 1) * (25 * ∑ v ∈ range (2 ^ q), (A * rhoE q s L j0 v) ^ p) := by
    unfold Sstar
    refine le_trans (sum_le_sum hstep) ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hΩ0 _)
  have hApow : ∑ v ∈ range (2 ^ q), (A * rhoE q s L j0 v) ^ p =
      A ^ p * ∑ v ∈ range (2 ^ q), rhoE q s L j0 v ^ p := by
    rw [mul_sum]; apply sum_congr rfl; intro v _; exact Real.mul_rpow hA0 (hrho0 v)
  have hmom := I_rho_moment s q L j0 p hp1 hq hL0 hj0
  have hA4p : A ^ p ≤ 4 ^ p := Real.rpow_le_rpow hA0 hA4 hp0.le
  have hΩp : Ω ^ (p - 1) = ((q : ℝ) + 2) ^ (2 * (p - 1)) := by
    rw [hΩ, Real.rpow_mul (by positivity), ← Real.rpow_natCast]; norm_num
  rw [hApow, hΩp] at hSstar
  have hsum0 : 0 ≤ ∑ v ∈ range (2 ^ q), rhoE q s L j0 v ^ p :=
    sum_nonneg fun v _ => Real.rpow_nonneg (hrho0 v) _
  have hX0 : 0 ≤ ((q : ℝ) + 2) ^ (2 * (p - 1)) := by positivity
  calc Sstar q s L j0 D p B ≤ ((q : ℝ) + 2) ^ (2 * (p - 1)) *
        (25 * (A ^ p * ∑ v ∈ range (2 ^ q), rhoE q s L j0 v ^ p)) := hSstar
    _ ≤ ((q : ℝ) + 2) ^ (2 * (p - 1)) * (25 * (4 ^ p *
        (2 ^ (p - 1) * ((2 : ℝ) ^ (tstar * hL s L + 1.1) * q * (q + 1)) ^ p *
          ((1 + rc ^ p) ^ q + 2 ^ q * ((1 + rc) / 2) ^ (p * (q - j0)))))) := by
        apply mul_le_mul_of_nonneg_left _ hX0
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hA4p hmom hsum0 (by positivity)
    _ = _ := by ring

end Collatz.M1
