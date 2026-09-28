import CollatzProof.M1.Explicit
import CollatzProof.M1.ExplicitNumV3
import CollatzProof.M1.ThmAV3
import CollatzProof.M1.S13B

/-!
# The main theorems of version 3 of the proof manuscript (revision r7 of the paper)

Checks the main theorems of §14.6 of version 3 of the proof manuscript (Sections 16.1 and 16.3 of the paper) with the same assembly as the explicit values of version 2 (`Explicit.lean`).
There are three differences from version 2 ((A) to (C) at the beginning of §14.6 of version 3 of the manuscript):
- **(A)** The supply of the lattice condition: instead of Proposition 13.2 (Theorem 2 of Bugeaud (2002), `c_D ≤ 9×10^{−4}`, `hgt`),
  Proposition 13.2B (the transcription `Bugeaud.Thm1G1 8` of Theorem 1, `c_D ≤ 9×10^{−3}`, `hgt_thm1`; §13.5.2 of version 3 of the manuscript, Proposition 15.5 of the paper).
- **(B)** Theorem A (v3) and Corollary A (v3) (`ThmAV3.lean`): `R_δ` is `RdeltaG 1.38 4.48 δ`, and the coefficient of the corollary is `2.18`.
- **(C)** The constants: `c_D = 9×10^{−3}`, `p = 247`, `ρ♯ = ρ_c + 10^{−4}`, `δ = 5.3116×10^{−6}` (the value `0.45𝔅 = 5.31165×10^{−6}` of the manuscript for `α = 0.6`,
  rounded down), `δ' = (19/9)δ`. The assembly of Proposition 14.1 passes `(a, b, E) = (1.38, 4.48, 2.2δ²)` and `hgt_thm1` to the general form `K_core_paramG` of
  `ExplicitCore.lean`.

Since `δ` is fixed independently of `α`, the condition `1.38δ < 1.5849×10^{−4}η` (`η = β_α − 1`; Lemma 14.0 (f) of the manuscript) for `ε_ρ ≤ 10^{−4}` in Lemma 6.4 (v3)
requires `η > 1.38δ/(1.5849×10^{−4}) = 0.046249`, i.e. `α > 0.51130`. Here we take `η ≥ 0.0465` and `α ≥ 0.5114`
(the rule of the manuscript chooses `δ ≤ 10^{−4}(β_α − 1)` for each `α` and so covers all `α > 1/2`; for `α ∈ [0.5114, 0.51294)` the `δ` here is larger than the `δ` of that rule,
but the condition (f) itself holds).
- `m1_v3` (range version): `F(α) ≤ α(1 − c) − ε` for `α ∈ [0.5114, 0.659]` and `ε < 2.18δ²(1 − α)`.
- `m1_v3_06`: `F(0.6) ≤ 0.6(1 − c) − 2.46×10^{−11}` (`2.18δ²·0.4 = 2.46018×10^{−11}`; `ε(0.6) ≥ 2.46×10^{−11}` of the manuscript).
- `sigma_v3`, `sigma_v3_06`: the versions for the stopping time `σ` (with `RhinHyp` added).
- `divergent_count_v3`: `#{n ≤ x | σ(n) = ∞} ≤ x^{1 − c − 5.84×10^{−11}}` (`g ≥ 5.84×10^{−11}` of Corollary 14.5 (v3) of the manuscript;
  with `α = 0.51294` as in the manuscript, `2.18δ²(1 − α)/α = 5.84014×10^{−11}`).
-/

namespace Collatz.M1

open Finset Filter Topology Bugeaud

/-! ## The constants of §14.6 of version 3 of the manuscript -/

/-- `δ = 0.45𝔅` of §14.6 of version 3 of the manuscript (`α = 0.6`) `= 5.31165×10^{−6}`, rounded down to `5.3116×10^{−6}`. -/
noncomputable def deltaV3 : ℝ := 5.3116e-6

/-- `δ' = (19/9)δ` of §14.6 of version 3 of the manuscript. -/
noncomputable def deltaV3' : ℝ := 19 / 9 * deltaV3

set_option maxHeartbeats 1000000 in
/-- The core of Proposition 14.1 (the constants of §14.6 of version 3 of the manuscript): `c_D = 9×10^{−3}`, `p = 247`, `ρ♯ = ρ_c + 10^{−4}`, `δ = 5.3116×10^{−6}`,
`δ' = (19/9)δ`, and `R_δ` of Definition 1.10 of v3. Assuming Theorem 1 (`Thm1G1 8`), it holds for `η ≥ 0.0465` (`s − q ≥ ηq`).
The conditions correspond to Lemma 14.0 of version 3 of the manuscript (Lemma 16.1 of the paper): (b) `κ_eff > 0` is the rate of the third term (`(2.2δ² + δ') log 2 + r_c^p/p < c_D v/2`, with `v` from `X_theta_phi247`),
(c) `4.48δ² ≤ 10^{−8}`, (d) `δ'·0.7 < c_D·0.2328/2`, (e) `δ' < 0.095η`, (f) `1.38δ < 1.5849×10^{−4}η`, (g) `c_D ≤ η/2`. -/
theorem K_core_v3 (hB1 : Thm1G1 8) (η : ℝ) (hη : 0.0465 ≤ η) :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s:ℝ) / q →
      (s:ℝ) / q ≤ 1.94 → η * q ≤ (s:ℝ) - q →
      ∀ L P, RdeltaG 1.38 4.48 deltaV3 s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(deltaV3' * q)) := by
  have hl2 := Real.log_two_lt_d9
  refine K_core_paramG 1.38 4.48 (2.2 * deltaV3 ^ 2) η deltaV3 deltaV3' 9e-3 (0.008378 * 0.2328) 1.6e-4
    247 (hgt_thm1 hB1 9e-3 (by norm_num) le_rfl) (by unfold deltaV3; norm_num)
    (by unfold deltaV3; norm_num) (by unfold deltaV3; norm_num) (by unfold deltaV3; norm_num)
    (by unfold deltaV3; norm_num) (by unfold deltaV3' deltaV3; norm_num)
    (by unfold deltaV3' deltaV3; norm_num) (by norm_num) (by linarith) (by norm_num) X_bp247 X_rc_pow247
    X_theta_phi247 ?_ (by unfold deltaV3' deltaV3; norm_num) (by unfold deltaV3' deltaV3; linarith)
    (by unfold deltaV3; linarith)
  have hpos : (0:ℝ) ≤ 2.2 * deltaV3 ^ 2 + deltaV3' := by unfold deltaV3' deltaV3; norm_num
  have := mul_le_mul_of_nonneg_left hl2.le hpos
  unfold deltaV3' deltaV3 at this ⊢
  push_cast
  norm_num at this ⊢
  linarith

/-- Proposition 14.1 (the constants of §14.6 of version 3 of the manuscript; Proposition 16.2 of the paper): for `α ∈ [0.5114, 0.659]` and all sufficiently large `K`,
`A_k ≤ 2^{−δ'q}` (`δ' = (19/9)δ`) for every slice of `R_δ` of v3 (`δ = 5.3116×10^{−6}`) and every shell.
The condition `α ≥ 0.5114` is needed for `β_α − 1 ≥ 0.0465`. -/
theorem all_shells_v3 (hB1 : Thm1G1 8) (α : ℝ) (hα : 0.5114 ≤ α) (hα' : α ≤ 0.659) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      ∀ L P, RdeltaG 1.38 4.48 deltaV3 (sOf α K) (K - sOf α K) L P → ∀ k ≤ L,
        Ak (K - sOf α K) (sOf α K) L P k ≤ (2:ℝ) ^ (-(deltaV3' * (K - sOf α K : ℕ))) := by
  have hη : 0.0465 ≤ (2 * α - 1) / (1 - α) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨q0, hcore⟩ := K_core_v3 hB1 _ hη
  obtain ⟨K0, hK0⟩ := sOf_ratio α (by linarith) hα' (max q0 1)
  refine ⟨K0, fun K hK L P hR k hk => ?_⟩
  obtain ⟨hq, hr1, hr2⟩ := hK0 K hK
  have hq1 : 1 ≤ K - sOf α K := le_trans (le_max_right _ _) hq
  refine hcore (sOf α K) (K - sOf α K) (le_trans (le_max_left _ _) hq) hr1 hr2 ?_ L P hR k hk
  exact X_sq_eta α (by linarith) K (by omega)

/-! ## The main theorems (v3) -/

/-- **Main theorem (Theorem 1.1 of the paper, explicit values, range version)**: assuming Theorem 1 of Bugeaud (2002) (`Thm1G1 8`), for `α ∈ [0.5114, 0.659]`,
`ε < 2.18δ²(1 − α)` (`δ = 5.3116×10^{−6}`, §14.6 of version 3 of the manuscript) and all sufficiently large `K`,
`#(𝒩_K ∩ [1, 2^{αK}]) ≤ 2^{(α(1−c) − ε)K}`. -/
theorem m1_v3 (hB1 : Thm1G1 8) (α : ℝ) (hα : 0.5114 ≤ α) (hα' : α ≤ 0.659) (ε : ℝ)
    (hε : ε < 2.18 * deltaV3 ^ 2 * (1 - α)) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨K0, hshell⟩ := all_shells_v3 hB1 α hα hα'
  have hδ : 0 < deltaV3 := by unfold deltaV3; norm_num
  have hδ1 : deltaV3 ≤ 1e-4 := by unfold deltaV3; norm_num
  obtain ⟨q0, hB⟩ := thmBG 1.38 4.48 deltaV3 deltaV3' (by unfold deltaV3; norm_num)
    (by unfold deltaV3; norm_num) (by unfold deltaV3' deltaV3; norm_num)
  obtain ⟨K1, hK1⟩ := sOf_ratio α (by linarith) hα' q0
  have hWF : ∃ K2 : ℕ, ∀ K ≥ K2, WFG 1.38 4.48 deltaV3 (sOf α K) (K - sOf α K) := by
    refine ⟨max K0 K1, fun K hK => ?_⟩
    obtain ⟨hq, hr1, hr2⟩ := hK1 K (le_trans (le_max_right _ _) hK)
    exact hB (sOf α K) (K - sOf α K) hq hr1 hr2
      (fun L P hR k hk => hshell K (le_trans (le_max_left _ _) hK) L P hR k hk)
  refine corA_v3 α deltaV3 (by linarith) hα' hδ hδ1 hWF ε (lt_min hε ?_)
  -- `2.18δ²(1 − α) ≤ 10^{−10} < (1 − c)(2α − 1)/2`
  obtain ⟨-, hc⟩ := cc_bounds
  have h1 : 2.18 * deltaV3 ^ 2 * (1 - α) ≤ 1e-10 := by
    have : 2.18 * deltaV3 ^ 2 ≤ 1e-10 := by unfold deltaV3; norm_num
    nlinarith
  have h2 : 1e-10 < (1 - cc) * (2 * α - 1) / 2 := by nlinarith
  linarith

/-- **Main theorem (Theorem 1.1 of the paper, explicit value, `α = 0.6`)**: `F(0.6) ≤ 0.6(1 − c) − 2.46×10^{−11}` (§14.6.3 of version 3 of the manuscript). -/
theorem m1_v3_06 (hB1 : Thm1G1 8) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (NKcount K ⌊(2:ℝ) ^ ((0.6:ℝ) * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((0.6 * (1 - cc) - 2.46e-11) * K) :=
  m1_v3 hB1 0.6 (by norm_num) (by norm_num) 2.46e-11 (by unfold deltaV3; norm_num)

/-- **Theorem 14.4 (Theorem 17.3 of the paper; stopping-time version, v3, range version)**: for `α ∈ [0.5114, 0.659]`, `ε < 2.18δ²(1 − α)` (`δ = 5.3116×10^{−6}`)
and all sufficiently large `K`, `#{n ≤ 2^{αK} | σ(n) > K} ≤ 2^{(α(1−c) − ε)K}`. -/
theorem sigma_v3 (hB1 : Thm1G1 8) (hR : RhinHyp) (α : ℝ) (hα : 0.5114 ≤ α) (hα' : α ≤ 0.659)
    (ε : ℝ) (hε : ε < 2.18 * deltaV3 ^ 2 * (1 - α)) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  set m := 2.18 * deltaV3 ^ 2 * (1 - α) with hm
  have hm1 : m ≤ 1e-10 := by
    have : 2.18 * deltaV3 ^ 2 ≤ 1e-10 := by unfold deltaV3; norm_num
    rw [hm]; nlinarith
  have ha : 0.4 ≤ α * (1 - cc) := by nlinarith
  exact sigma_of_NK hR α ((ε + m) / 2) ε (by linarith) (by linarith)
    (m1_v3 hB1 α hα hα' ((ε + m) / 2) (by linarith))

/-- **Theorem 14.4 (Theorem 17.3 of the paper; stopping-time version, v3, `α = 0.6`)**: `F_σ(0.6) ≤ 0.6(1 − c) − 2.46×10^{−11}`.
The hypotheses are Theorem 1 of Bugeaud (2002) and the Rhin-type bound (`RhinHyp`, proved from Mazur's formalization in `CollatzND/M1ExplicitV3.lean`). -/
theorem sigma_v3_06 (hB1 : Thm1G1 8) (hR : RhinHyp) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ ((0.6:ℝ) * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((0.6 * (1 - cc) - 2.46e-11) * K) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  exact sigma_of_NK hR 0.6 2.4601e-11 2.46e-11 (by norm_num) (by nlinarith)
    (m1_v3 hB1 0.6 (by norm_num) (by norm_num) 2.4601e-11 (by unfold deltaV3; norm_num))

/-- **Corollary 14.5 (Corollary 17.4 of the paper; integers with infinite stopping time, v3)**: for all sufficiently large `x`, `#{n ≤ x | σ(n) = ∞} ≤ x^{1 − c − 5.84×10^{−11}}`.
With `α = 0.51294` as in §14.6.3 of version 3 of the manuscript (`β_α − 1 = 0.053135 ≥ 0.0465`; the rule `δ = min(0.45𝔅, 10^{−4}(β_α − 1))` of the manuscript also gives `0.45𝔅` here):
`2.18δ²(1 − α) = 2.995640×10^{−11}`, `ε₁ = 2.99562×10^{−11}`, `ε = 2.9956×10^{−11}`, `ε/α = 5.840059×10^{−11} > 5.84×10^{−11}`. -/
theorem divergent_count_v3 (hB1 : Thm1G1 8) (hR : RhinHyp) :
    ∃ x0 : ℕ, ∀ x ≥ x0, (DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - cc - 5.84e-11) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  refine div_of_sigma 0.51294 2.9956e-11 5.84e-11 (by norm_num) (by norm_num) ?_
  exact sigma_of_NK hR 0.51294 2.99562e-11 2.9956e-11 (by norm_num) (by nlinarith)
    (m1_v3 hB1 0.51294 (by norm_num) (by norm_num) 2.99562e-11 (by unfold deltaV3; norm_num))

/-! ## The qualitative forms from Theorem 1 alone (all `α ∈ (1/2, 0.659]`) -/

/-- From Proposition 13.2B: the supply of the lattice condition for the window widths `c_D ≤ 9×10^{−4}` needed by the chain of version 2. -/
theorem hgt_supply_thm1 (hB1 : Thm1G1 8) : ∀ cD : ℝ, 0 < cD → cD ≤ 9e-4 → HgtSupply cD :=
  fun cD h0 h1 => hgt_thm1 hB1 cD h0 (by linarith)

/-- **Main theorem (Theorem 1.1 of the paper, range version, qualitative form)** from Theorem 1 of Bugeaud (2002) (`Thm1G1 8`) alone: for every `α ∈ (1/2, 0.659]`
there are `ε > 0` and `K₀` such that `#(𝒩_K ∩ [1, 2^{αK}]) ≤ 2^{(α(1−c) − ε)K}` for all `K ≥ K₀`. -/
theorem m1_main_thm1 (hB1 : Thm1G1 8) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
    ∃ ε > 0, ∃ K0 : ℕ, ∀ K ≥ K0,
      (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) :=
  m1_mainG (hgt_supply_thm1 hB1) α hα hα'

/-- **Theorem 14.4 (stopping-time version, qualitative form)** from Theorem 1. -/
theorem sigma_main_thm1 (hB1 : Thm1G1 8) (hR : RhinHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
    ∃ ε > 0, ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) :=
  sigma_mainG (hgt_supply_thm1 hB1) hR α hα hα'

/-- **Corollary 14.5 (qualitative form)** from Theorem 1. -/
theorem divergent_count_thm1 (hB1 : Thm1G1 8) (hR : RhinHyp) :
    ∃ ε > 0, ∃ x0 : ℕ, ∀ x ≥ x0, (DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - cc - ε) :=
  divergent_countG (hgt_supply_thm1 hB1) hR

end Collatz.M1
