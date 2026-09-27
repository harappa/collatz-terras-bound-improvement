import CollatzProof.M1.Defs

/-!
# Definitions for §1.6 and §3: the Fourier transform, the tail statistic, condition (WF)
-/

namespace Collatz.M1

open Finset

/-- `e(x) = e^{2πix}`. -/
noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `Ê(ξ) = Σ_{z∈E} e(−ξz/2^q)` (`ξ` is an integer; a function of `ξ mod 2^q`). -/
noncomputable def Ehat (q : ℕ) (E : Finset ℕ) (ξ : ℤ) : ℂ :=
  ∑ z ∈ E, eC (-((ξ : ℝ) * z) / 2 ^ q)

/-- `W = Σ_{ξ≠0} |Ê(ξ)|²` (`ξ` ranges over the representatives in `[1, 2^q)`). -/
noncomputable def Wsum (q : ℕ) (E : Finset ℕ) : ℝ :=
  ∑ ξ ∈ (range (2 ^ q)).erase 0, ‖Ehat q E ξ‖ ^ 2

/-- `⟨2^{−t} x⟩_{3^n}`: the least nonnegative residue of `2^{−t}x` modulo `3^n`. -/
noncomputable def inv2mod (t n : ℕ) (x : ℤ) : ℕ :=
  ((x : ZMod (3 ^ n)) * ((2 : ZMod (3 ^ n)) ^ t)⁻¹).val

/-- The tail statistic `G(τ) = a_τ − 3^{L'}⟨2^{−t} m_τ⟩_{3^{L_p}}` (§3.2, `t = s − P`, `L' = L − L_p`). -/
noncomputable def Gstat (q s L P : ℕ) (τ : Fin (s - P) → Bool) : ℤ :=
  (aOf τ : ℤ) - 3 ^ (L - Lp q) * (inv2mod (s - P) (Lp q) (mOf τ) : ℤ)

/-- `Ĝ(ξ) = Σ_{τ∈𝒯} e(ξ G(τ)/2^q)`. -/
noncomputable def Ghat (q s L P : ℕ) (ξ : ℤ) : ℂ :=
  ∑ τ ∈ Tset q s L P, eC ((ξ : ℝ) * (Gstat q s L P τ : ℝ) / 2 ^ q)

/-- `Λ_{L,P} = Σ_{ξ≠0} |Ê(ξ)|²|Ĝ(ξ)|² / (|E|²|𝒯|²)` (Definition 3.4, `E = E_L`). -/
noncomputable def LamLP (q s L P : ℕ) : ℝ :=
  (∑ ξ ∈ (range (2 ^ q)).erase 0,
      ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2 * ‖Ghat q s L P ξ‖ ^ 2) /
    (((Eset q (hL s L)).card : ℝ) ^ 2 * ((Tset q s L P).card : ℝ) ^ 2)

/-- Condition (WF)(δ) (Definition 3.4): `Λ_{L,P} ≤ 2^{(c−2δ)q}` for every slice in `R_δ`. -/
def WF (δ : ℝ) (s q : ℕ) : Prop :=
  ∀ L P : ℕ, Rdelta δ s q L P → LamLP q s L P ≤ (2:ℝ) ^ ((cc - 2 * δ) * q)

/-- `s = ⌊αK⌋ + 1` (Corollary A, §14.1). -/
noncomputable def sOf (α : ℝ) (K : ℕ) : ℕ := ⌊α * K⌋₊ + 1

end Collatz.M1
