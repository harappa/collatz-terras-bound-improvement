import CollatzProof.M1.ShellDefs

/-!
# Definitions for §10–§13: the measure on deep frequencies, `S_p^*`, the autocorrelation, the lattice condition, and Bugeaud's (2002) theorem (as a hypothesis)
-/

namespace Collatz.M1

open Finset

variable (q s L : ℕ)

/-- The probability measure on deep frequencies `μ(ξ) = |Ê(ξ)|² 1[ξ≠0, dep(ξ)>j₀] / ((1−ϖ_{j₀})W)` (Definition 10.1, `ξ ∈ [0, 2^q)`). -/
noncomputable def muDeep (j0 : ℕ) (ξ : ℕ) : ℝ :=
  if ξ ≠ 0 ∧ j0 < dep q ξ then
    ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 / ((1 - varpi q s L j0) * Wsum q (Eset q (hL s L)))
  else 0

/-- `κ₀(ξ) = ⌊(3^L ξ + 2^{q−1})/2^q⌋`. -/
def kappa0 (ξ : ℕ) : ℤ := ((3 ^ L * ξ + 2 ^ (q - 1) : ℕ) / 2 ^ q : ℕ)

/-- `φ_p = (2^{−p'} + 2^{1−2p'})^{1/p'}`, `p' = p/(p−1)`. -/
noncomputable def phiP (p : ℝ) : ℝ :=
  ((2:ℝ) ^ (-(p / (p - 1))) + (2:ℝ) ^ (1 - 2 * (p / (p - 1)))) ^ (1 / (p / (p - 1)))

/-- `𝔼_μ e(h κ₀(ξ)/2^D + βξ/2^q)`. -/
noncomputable def muChar (j0 D : ℕ) (h : ℕ) (β : ℝ) : ℂ :=
  ∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) *
    eC ((h : ℝ) * (kappa0 q L ξ : ℝ) / 2 ^ D + β * ξ / 2 ^ q)

/-- `S_p^*(B) = Σ_{h=1}^{2^D−1} sup_{|β|≤B} |𝔼_μ e(hκ₀/2^D + βξ/2^q)|^p` (Definition 10.1). -/
noncomputable def Sstar (j0 D : ℕ) (p B : ℝ) : ℝ :=
  ∑ h ∈ Ico 1 (2 ^ D), ⨆ β : Set.Icc (-B) B, ‖muChar q s L j0 D h β‖ ^ p

/-- The autocorrelation of the deep part, `r^{deep}(v) = 2^{−q} Σ_{ξ≠0, dep>j₀} |Ê(ξ)|² e(vξ/2^q)` (§11). -/
noncomputable def rDeep (j0 : ℕ) (v : ℕ) : ℂ :=
  (2:ℂ)⁻¹ ^ q * ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => j0 < dep q ξ),
    (‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 : ℂ) * eC ((v : ℝ) * ξ / 2 ^ q)

/-- `ϱ_E(v) = |r^{deep}(v)|/|E|`. -/
noncomputable def rhoE (j0 : ℕ) (v : ℕ) : ℝ :=
  ‖rDeep q s L j0 v‖ / (Eset q (hL s L)).card

/-- Every nonzero element of the lattice `Λ_L = {(n, m) | m ≡ n3^L (mod 2^{q+D})}` has sup norm at least `H` (§11.3, Proposition 13.2).
**The argument order is `LatticeCond q L D H`** (the binders are now explicit. In the first version of the skeleton the automatic inclusion of `variable`s gave this same order, but
S11 and S13 called it in the order `q D L`, which made the statement false. Found by an independent check, 2026-09-25). -/
def LatticeCond (q L D : ℕ) (H : ℝ) : Prop :=
  ∀ a b : ℤ, (a, b) ≠ (0, 0) → a ≡ 3 ^ L * b [ZMOD 2 ^ (q + D)] → H ≤ max |a| |b|

/-! ## Theorem 2 of Bugeaud (2002) (hypothesis; `m = 8`, `μ = 4`, `c₂(4) = 53.6` in the multiplicatively independent case)

The statement of the theorem in the original paper (Compositio Math. 132 (2002) 137–158, pp. 138–140; checked against the original, see Theorem 15.1 of the paper), written out for the case used here,
`m = 8 = 2^3` (`w = 1`, `p₁ = 2`, `u₁ = 3`), `μ = 4` (Theorem 13.1 of the proof manuscript).
- `v_m` is the `m`-adic valuation: `v_8(x) = ⌊v_2(x)/3⌋` for an integer `x ≠ 0`, and `v_8(a) − v_8(b)` for a rational number `a/b` in lowest terms.
- Hypotheses: `x₁/y₁`, `x₂/y₂` are nonzero rational numbers, `x₁/y₁ ≠ ±1`, `v_2(x_i/y_i) = 0`; (H1) for an odd `g ≥ 1`, `v_2((x₁/y₁)^g − 1) ≥ 3` and `v_2((x₂/y₂)^g − 1) ≥ 1`;
  (H2) `v_2((x_i/y_i)^g − 1) ≥ 2`; `b₁, b₂ ≥ 1`, and 2 does not divide both `b₁` and `b₂` (the original paper's "`m, b₁, b₂` are coprime", remark on p. 140). Here, as a precaution, we assume the narrower condition "`b₂` is odd" (it is also satisfied under the reading "`p_i ∤ b₂/p_i^{h_i}`" of Theorem 1; this work uses only `b₂ = 1`; narrowing the hypothesis weakens the external theorem being asserted, and so reduces the risk of assuming something false); `x₁/y₁` and `x₂/y₂` are multiplicatively independent;
  `A_i > 1` with `log A_i ≥ max(log|x_i|, log|y_i|, log 8)` (numerator and denominator in lowest terms).
- Conclusion: for `Λ = (x₁/y₁)^{b₁} − (x₂/y₂)^{b₂}`,
  `v_8(Λ) ≤ 53.6 g/(log 8)^4 · (max(log b' + log log 8 + 0.64, 4 log 8))² log A₁ log A₂`, where `b' = b₁/log A₂ + b₂/log A₁`. -/

/-- The 8-adic valuation `v_8` of a rational number (for nonzero rational numbers). -/
noncomputable def v8 (x : ℚ) : ℤ :=
  ((padicValInt 2 x.num / 3 : ℕ) : ℤ) - ((padicValNat 2 x.den / 3 : ℕ) : ℤ)

/-- The 2-adic valuation of a rational number. -/
noncomputable def v2q (x : ℚ) : ℤ := padicValRat 2 x

/-- Two rational numbers are multiplicatively independent. -/
def MulIndep (r₁ r₂ : ℚ) : Prop := ∀ k₁ k₂ : ℤ, r₁ ^ k₁ * r₂ ^ k₂ = 1 → k₁ = 0 ∧ k₂ = 0

/-- **Hypothesis**: Theorem 2 of Bugeaud (2002) (`m = 8`, `μ = 4`, independent case). -/
def BugeaudHyp : Prop :=
  ∀ (r₁ r₂ : ℚ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ),
    r₁ ≠ 0 → r₂ ≠ 0 → r₁ ≠ 1 → r₁ ≠ -1 → v2q r₁ = 0 → v2q r₂ = 0 →
    1 ≤ g → g % 2 = 1 → 3 ≤ v2q (r₁ ^ g - 1) → 2 ≤ v2q (r₂ ^ g - 1) →
    1 ≤ b₁ → 1 ≤ b₂ → b₂ % 2 = 1 → MulIndep r₁ r₂ →
    1 < A₁ → 1 < A₂ →
    Real.log |(r₁.num : ℝ)| ≤ Real.log A₁ → Real.log (r₁.den : ℝ) ≤ Real.log A₁ → Real.log 8 ≤ Real.log A₁ →
    Real.log |(r₂.num : ℝ)| ≤ Real.log A₂ → Real.log (r₂.den : ℝ) ≤ Real.log A₂ → Real.log 8 ≤ Real.log A₂ →
    (v8 (r₁ ^ b₁ - r₂ ^ b₂) : ℝ) ≤
      53.6 * g / (Real.log 8) ^ 4 *
        (max (Real.log (b₁ / Real.log A₂ + b₂ / Real.log A₁) + Real.log (Real.log 8) + 0.64)
          (4 * Real.log 8)) ^ 2 * Real.log A₁ * Real.log A₂

end Collatz.M1
