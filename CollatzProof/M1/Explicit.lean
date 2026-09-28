import CollatzProof.M1.Sigma
import CollatzProof.M1.ExplicitCore

/-!
# Explicit values of the main theorem (version 2 of the proof manuscript): the main theorem, the stopping-time version and the corollary on divergent orbits

Checks the explicit values of §14.3 (main theorem) and §14.5 (Theorem 14.4, Corollary 14.5) of version 2 of the proof manuscript (the values of revision r6 of the paper).
- `m1_explicit`: `F(α) ≤ α(1 − c) − ε` for `α ∈ [0.5006, 0.659]` and `ε < 1.70δ²(1 − α)` (`δ = 2.8055×10^{−7}`).
  In particular `m1_explicit_06`: `F(0.6) ≤ 0.6(1 − c) − 5.35×10^{−14}` (`1.70δ²·0.4 = 5.35216×10^{−14}`).
- `sigma_explicit_06`: the same exponent for the stopping time `σ` (the polynomial term of `sigma_le_NK` is absorbed by the margin `ε₁ = 5.351×10^{−14}`).
- `divergent_count_explicit`: `#{n ≤ x | σ(n) = ∞} ≤ x^{1 − c − 1.33×10^{−13}}` (with `α = 0.501` as in Corollary 14.5 of the manuscript,
  `1.70δ²(1 − α)/α = 1.3327×10^{−13}`).

The qualitative forms (`m1_main`, `sigma_main`, `divergent_count`) halve `ε` to create a margin; here the statements take any strictly smaller `ε` instead
(`corA` accepts every `ε < min(1.70δ²(1−α), (1−c)(2α−1)/2)`).
-/

namespace Collatz.M1

open Finset Filter Topology

/-- **Main theorem (Theorem 1.1 of the paper; explicit values of version 2, range version)**: assuming Theorem 2 of Bugeaud (2002), for `α ∈ [0.5006, 0.659]` and
`ε < 1.70δ²(1 − α)` (`δ = 2.8055×10^{−7}`, §14.1 of the manuscript) and all sufficiently large `K`,
`#(𝒩_K ∩ [1, 2^{αK}]) ≤ 2^{(α(1−c) − ε)K}`. -/
theorem m1_explicit (hBug : BugeaudHyp) (α : ℝ) (hα : 0.5006 ≤ α) (hα' : α ≤ 0.659) (ε : ℝ)
    (hε : ε < 1.70 * deltaE ^ 2 * (1 - α)) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨K0, hshell⟩ := all_shells_explicit hBug α hα hα'
  have hδ : 0 < deltaE := by unfold deltaE; norm_num
  have hδ1 : deltaE ≤ 1e-3 := by unfold deltaE; norm_num
  have hδ' : 2 * deltaE < deltaE' := by unfold deltaE' deltaE; norm_num
  obtain ⟨q0, hB⟩ := thmB deltaE deltaE' hδ hδ1 hδ'
  obtain ⟨K1, hK1⟩ := sOf_ratio α (by linarith) hα' q0
  have hWF : ∃ K2 : ℕ, ∀ K ≥ K2, WF deltaE (sOf α K) (K - sOf α K) := by
    refine ⟨max K0 K1, fun K hK => ?_⟩
    obtain ⟨hq, hr1, hr2⟩ := hK1 K (le_trans (le_max_right _ _) hK)
    exact hB (sOf α K) (K - sOf α K) hq hr1 hr2
      (fun L P hR k hk => hshell K (le_trans (le_max_left _ _) hK) L P hR k hk)
  refine corA α deltaE (by linarith) hα' hδ hδ1 hWF ε (lt_min hε ?_)
  -- `1.70δ²(1 − α) ≤ 10^{−12} < (1 − c)(2α − 1)/2`
  obtain ⟨-, hc⟩ := cc_bounds
  have h1 : 1.70 * deltaE ^ 2 * (1 - α) ≤ 1e-12 := by
    have : 1.70 * deltaE ^ 2 ≤ 1e-12 := by unfold deltaE; norm_num
    nlinarith
  have h2 : 1e-12 < (1 - cc) * (2 * α - 1) / 2 := by nlinarith
  linarith

/-- **Main theorem (Theorem 1.1 of the paper; explicit value of version 2, `α = 0.6`)**: `F(0.6) ≤ 0.6(1 − c) − 5.35×10^{−14}` (§14.3 of the manuscript). -/
theorem m1_explicit_06 (hBug : BugeaudHyp) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (NKcount K ⌊(2:ℝ) ^ ((0.6:ℝ) * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((0.6 * (1 - cc) - 5.35e-14) * K) :=
  m1_explicit hBug 0.6 (by norm_num) (by norm_num) 5.35e-14 (by unfold deltaE; norm_num)

/-- The transfer by Lemmas 14.2, 14.3 and Theorem 14.4 (explicit form): from the exponent `α(1 − c) − ε₁` of the bound on the count for `κ_coef`,
the bound `2^{(α(1−c) − ε)K}` on the count for `σ` for every `ε < ε₁` (with `ε < α(1 − c)`), for all sufficiently large `K`. -/
theorem sigma_of_NK (hR : RhinHyp) (α ε₁ ε : ℝ) (hεε : ε < ε₁) (hεa : ε < α * (1 - cc))
    (hN : ∃ K1 : ℕ, ∀ K ≥ K1,
      (NKcount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε₁) * K)) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨K1, hK1⟩ := hN
  obtain ⟨C, κ, hC, hκ, hS⟩ := sigma_le_NK hR
  set a := α * (1 - cc) with ha
  have ev1 := K_sg_poly C κ (a - ε) (by linarith)
  have ev2 : ∀ᶠ K : ℕ in atTop, 1 ≤ (ε₁ - ε) * K := by
    filter_upwards [eventually_ge_atTop ⌈1 / (ε₁ - ε)⌉₊] with K hK
    have h1 : 1 / (ε₁ - ε) ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
    rw [div_le_iff₀ (by linarith)] at h1; linarith
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp ((ev1.and ev2).and (eventually_ge_atTop (max K1 1)))
  refine ⟨K0, fun K hK => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hK0 K hK
  have hN := hK1 K (le_trans (le_max_left _ _) h3)
  have hSK := hS K ⌊(2:ℝ) ^ (α * K)⌋₊ (le_trans (le_max_right _ _) h3)
  have h4 : (2:ℝ) ^ ((a - ε₁) * K) ≤ (2:ℝ) ^ ((a - ε) * K) / 2 := by
    rw [← Real.rpow_sub_one (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have h5 : (2:ℝ) ^ ((a - ε) * K) / 2 + (2:ℝ) ^ ((a - ε) * K) / 2 = (2:ℝ) ^ ((a - ε) * K) := by
    ring
  linarith

/-- **Theorem 14.4 (stopping-time version, explicit values of version 2, range version)**: for `α ∈ [0.5006, 0.659]`, `ε < 1.70δ²(1 − α)` (`δ = 2.8055×10^{−7}`)
and all sufficiently large `K`, `#{n ≤ 2^{αK} | σ(n) > K} ≤ 2^{(α(1−c) − ε)K}`. -/
theorem sigma_explicit (hBug : BugeaudHyp) (hR : RhinHyp) (α : ℝ) (hα : 0.5006 ≤ α) (hα' : α ≤ 0.659)
    (ε : ℝ) (hε : ε < 1.70 * deltaE ^ 2 * (1 - α)) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  set m := 1.70 * deltaE ^ 2 * (1 - α) with hm
  have hm1 : m ≤ 1e-12 := by
    have : 1.70 * deltaE ^ 2 ≤ 1e-12 := by unfold deltaE; norm_num
    rw [hm]; nlinarith
  have ha : 0.4 ≤ α * (1 - cc) := by nlinarith
  exact sigma_of_NK hR α ((ε + m) / 2) ε (by linarith) (by linarith)
    (m1_explicit hBug α hα hα' ((ε + m) / 2) (by linarith))

/-- **Theorem 14.4 (stopping-time version, explicit value of version 2, `α = 0.6`)**: `F_σ(0.6) ≤ 0.6(1 − c) − 5.35×10^{−14}`.
The hypotheses are Theorem 2 of Bugeaud (2002) and the Rhin-type bound (`RhinHyp`, proved from Mazur's formalization in `CollatzND/M1Explicit.lean`). -/
theorem sigma_explicit_06 (hBug : BugeaudHyp) (hR : RhinHyp) :
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ ((0.6:ℝ) * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((0.6 * (1 - cc) - 5.35e-14) * K) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  exact sigma_of_NK hR 0.6 5.351e-14 5.35e-14 (by norm_num) (by nlinarith)
    (m1_explicit hBug 0.6 (by norm_num) (by norm_num) 5.351e-14 (by unfold deltaE; norm_num))

/-- The assembly of Corollary 14.5 (explicit form): from the exponent `α(1 − c) − ε` of the bound on the count for `σ`, for every `ε₂ < ε/α`,
`#{n ≤ x | σ(n) = ∞} ≤ x^{1 − c − ε₂}` (for all sufficiently large `x`). -/
theorem div_of_sigma (α ε ε₂ : ℝ) (hα0 : 0 < α) (hε2 : ε₂ < ε / α)
    (hS : ∃ K0 : ℕ, ∀ K ≥ K0,
      (SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ : ℝ) ≤ (2:ℝ) ^ ((α * (1 - cc) - ε) * K)) :
    ∃ x0 : ℕ, ∀ x ≥ x0, (DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - cc - ε₂) := by
  classical
  obtain ⟨K0, hK0⟩ := hS
  set e : ℝ := α * (1 - cc) - ε with he
  set g : ℝ := ε / α - ε₂ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  refine ⟨max (max ⌈(2:ℝ) ^ (α * K0)⌉₊ ⌈(2:ℝ) ^ (|e| / g)⌉₊) 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (1:ℝ) ≤ x := by exact_mod_cast hx1
  have hx0 : (0:ℝ) < x := by linarith
  have hxA : (2:ℝ) ^ (α * K0) ≤ x :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  have hxB : (2:ℝ) ^ (|e| / g) ≤ x :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  set Lx := Real.logb 2 x with hLx
  have hL0 : 0 ≤ Lx := Real.logb_nonneg (by norm_num) hxR
  have h2L : (2:ℝ) ^ Lx = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  set K := ⌈Lx / α⌉₊ with hK
  have hK1 : Lx / α ≤ K := Nat.le_ceil _
  have hLK : Lx ≤ α * K := by rw [div_le_iff₀ hα0] at hK1; linarith
  -- K ≥ K0
  have hKK0 : K0 ≤ K := by
    have : α * K0 ≤ Lx := by
      rw [hLx, Real.le_logb_iff_rpow_le (by norm_num) hx0]; exact hxA
    have : (K0:ℝ) ≤ K := by
      have : (K0:ℝ) ≤ Lx / α := by rw [le_div_iff₀ hα0]; linarith
      linarith
    exact_mod_cast this
  -- x ≤ ⌊2^{αK}⌋
  have hxfl : x ≤ ⌊(2:ℝ) ^ (α * K)⌋₊ := by
    apply Nat.le_floor
    rw [← h2L]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hLK
  have hDiv : DivCount x ≤ SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ := by
    unfold DivCount SigmaCount
    apply card_le_card
    intro n hn
    rw [mem_filter, mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hxfl⟩, hn.2 K⟩
  have hS := hK0 K hKK0
  -- 2^{eK} ≤ 2^{|e|} x^{e/α}
  have h1 : e * K ≤ Lx * (e / α) + |e| := by
    have e1 : Lx * (e / α) = e * (Lx / α) := by ring
    rw [e1]
    have hK2 : (K:ℝ) < Lx / α + 1 := Nat.ceil_lt_add_one (div_nonneg hL0 hα0.le)
    rcases le_total 0 e with hpos | hneg
    · rw [abs_of_nonneg hpos]; nlinarith
    · have : e * K ≤ e * (Lx / α) := mul_le_mul_of_nonpos_left hK1 hneg
      linarith [abs_nonneg e]
  have h2 : (2:ℝ) ^ (e * K) ≤ x ^ (e / α) * (2:ℝ) ^ |e| := by
    calc (2:ℝ) ^ (e * K) ≤ (2:ℝ) ^ (Lx * (e / α) + |e|) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = x ^ (e / α) * (2:ℝ) ^ |e| := by
          rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), h2L]
  have h3 : (2:ℝ) ^ |e| ≤ x ^ g := by
    have := Real.rpow_le_rpow (by positivity) hxB hg0.le
    rwa [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hg0.ne'] at this
  have h4 : x ^ (e / α) * x ^ g = (x:ℝ) ^ (1 - cc - ε₂) := by
    rw [← Real.rpow_add hx0]; congr 1; rw [he, hg]; field_simp; ring
  have hxe : 0 ≤ (x:ℝ) ^ (e / α) := Real.rpow_nonneg hx0.le _
  calc (DivCount x : ℝ) ≤ SigmaCount K ⌊(2:ℝ) ^ (α * K)⌋₊ := by exact_mod_cast hDiv
    _ ≤ (2:ℝ) ^ (e * K) := hS
    _ ≤ x ^ (e / α) * (2:ℝ) ^ |e| := h2
    _ ≤ x ^ (e / α) * x ^ g := mul_le_mul_of_nonneg_left h3 hxe
    _ = (x:ℝ) ^ (1 - cc - ε₂) := h4

/-- **Corollary 14.5 (integers with infinite stopping time, explicit value of version 2)**: for all sufficiently large `x`, `#{n ≤ x | σ(n) = ∞} ≤ x^{1 − c − 1.33×10^{−13}}`.
With `α = 0.501` as in the manuscript (`β_α − 1 = 0.004008 ≥ 0.0022`): `1.70δ²(1 − α) = 6.6768×10^{−14}`, `ε₁ = 6.675×10^{−14}`,
`ε = 6.67×10^{−14}`, `ε/α = 1.33134×10^{−13} > 1.33×10^{−13}`. -/
theorem divergent_count_explicit (hBug : BugeaudHyp) (hR : RhinHyp) :
    ∃ x0 : ℕ, ∀ x ≥ x0, (DivCount x : ℝ) ≤ (x : ℝ) ^ (1 - cc - 1.33e-13) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  refine div_of_sigma 0.501 6.67e-14 1.33e-13 (by norm_num) (by norm_num) ?_
  exact sigma_of_NK hR 0.501 6.675e-14 6.67e-14 (by norm_num) (by nlinarith)
    (m1_explicit hBug 0.501 (by norm_num) (by norm_num) 6.675e-14 (by unfold deltaE; norm_num))

end Collatz.M1
