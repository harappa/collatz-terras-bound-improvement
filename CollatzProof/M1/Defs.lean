import CollatzProof.Fiber

/-!
# Formalization of version 2 of the proof manuscript: common definitions (§1)

Notation of §1 of the manuscript (Section 3 of the paper). Namespace `Collatz.M1`.
- A word is a `Fin n → Bool` (`true` is an odd step). The parity word of length `len` of a number `n` is `pw n len`.
- The Terras number `mOf x` of a word (the element of `[0, 2^n)` whose parity word is `x`, Lemma 1.1).
-/

namespace Collatz.M1

open Finset

/-! ## Constants (§1.4) -/

/-- `λ = log₂ 3`. -/
noncomputable def lam : ℝ := Real.logb 2 3
/-- `a = λ − 1` (the increase of the height at an odd step). -/
noncomputable def aa : ℝ := lam - 1
/-- `ρ_c = 1/λ`. -/
noncomputable def rhoc : ℝ := 1 / lam
/-- The binary entropy (in bits). -/
noncomputable def Hb (ρ : ℝ) : ℝ := -(ρ * Real.logb 2 ρ) - (1 - ρ) * Real.logb 2 (1 - ρ)
/-- `c = 1 − H(ρ_c)`. -/
noncomputable def cc : ℝ := 1 - Hb rhoc
/-- `t* = log₂(1/a)/λ`. -/
noncomputable def tstar : ℝ := Real.logb 2 (1 / aa) / lam
/-- `f = 2^{−c}`. -/
noncomputable def ff : ℝ := (2:ℝ) ^ (-cc)
/-- `r_c = 2√(ρ_c(1−ρ_c))`. -/
noncomputable def rc : ℝ := 2 * Real.sqrt (rhoc * (1 - rhoc))
/-- `Θ_γ(ρ) = 1 − 2(1−γ)ρ(1−ρ)`. -/
noncomputable def Theta (γ ρ : ℝ) : ℝ := 1 - 2 * (1 - γ) * ρ * (1 - ρ)

/-! ## Words, heights, survival (§1.1, §1.2) -/

/-- The parity word `u_len(n)` of length `len` of a number `n` (`true` iff `T^i(n)` is odd). -/
def pw (n len : ℕ) : Fin len → Bool := fun i => decide (T^[i] n % 2 = 1)

/-- The number `o_j(x)` of 1s among the first `j` letters of the word `x`. -/
def ones {n : ℕ} (x : Fin n → Bool) (j : ℕ) : ℕ :=
  (univ.filter (fun i : Fin n => (i : ℕ) < j ∧ x i = true)).card

/-- The height `y_j(x) = y + λ o_j(x) − j`. -/
noncomputable def hw {n : ℕ} (y : ℝ) (x : Fin n → Bool) (j : ℕ) : ℝ :=
  y + lam * (ones x j : ℝ) - j

/-- The word `x` survives from height `y`: the height is at least 0 for all `1 ≤ j ≤ n`. -/
def SurvW {n : ℕ} (y : ℝ) (x : Fin n → Bool) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 ≤ hw y x j

/-- `#(𝒩_K ∩ [1, X])` (Definition 1.3: `n ≥ 1` whose word of length `K` survives from height 0). -/
noncomputable def NKcount (K X : ℕ) : ℕ := by
  classical
  exact ((Icc 1 X).filter (fun n => SurvW 0 (pw n K))).card

/-! ## Terras numbers (the inverse of the bijection of Lemma 1.1) -/

/-- Lemma 1.1: `m ↦ pw m n` from `[0, 2^n)` to `{0,1}^n` is a bijection. -/
theorem pw_bijective (n : ℕ) :
    Function.Bijective (fun m : Fin (2 ^ n) => pw (m : ℕ) n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro m m' h
  apply Fin.ext
  apply terras_inj n m m' m.2 m'.2
  intro i hi
  have := congrFun h ⟨i, hi⟩
  simp only [pw] at this
  have h1 := Nat.mod_two_eq_zero_or_one (T^[i] (m:ℕ))
  have h2 := Nat.mod_two_eq_zero_or_one (T^[i] (m':ℕ))
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/-- The Terras bijection `Fin (2^n) ≃ (Fin n → Bool)`. -/
noncomputable def terrasEquiv (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  Equiv.ofBijective _ (pw_bijective n)

/-- The Terras number `m_x ∈ [0, 2^n)` of the word `x`. -/
noncomputable def mOf {n : ℕ} (x : Fin n → Bool) : ℕ := ((terrasEquiv n).symm x : ℕ)

/-- `a_x = T^n(m_x)` (Lemma 1.2 (ii)). -/
noncomputable def aOf {n : ℕ} (x : Fin n → Bool) : ℕ := T^[n] (mOf x)

/-- `c_x` (the additive term of Lemma 1.2): `2^n T^n(m_x) = 3^{|x|} m_x + c_x`. -/
noncomputable def cOf {n : ℕ} (x : Fin n → Bool) : ℕ := c (mOf x) n

/-! ## Layers, slices, survival sets (§1.3, §1.5) -/

/-- The height at the end of a layer, `h_L = λL − s`. -/
noncomputable def hL (s L : ℕ) : ℝ := lam * L - s

/-- `𝒜_L` (Definition 1.4): the words of length `s` with `L` 1s that survive from height 0. -/
noncomputable def Aset (s L : ℕ) : Finset (Fin s → Bool) := by
  classical
  exact univ.filter (fun u => ones u s = L ∧ SurvW 0 u)

/-- The survival set `E ⊂ [0, 2^q)`: the `z` whose word of length `q` survives from height `y` (Definition 1.4 takes `y = h_L`). -/
noncomputable def Eset (q : ℕ) (y : ℝ) : Finset ℕ := by
  classical
  exact (range (2 ^ q)).filter (fun z => SurvW y (pw z q))

/-- `L_p = max{l | 3^l ≤ 2^q}` (§1.5). -/
def Lp (q : ℕ) : ℕ := Nat.findGreatest (fun l => 3 ^ l ≤ 2 ^ q) q

/-- `h_p = λ L_p − P`. -/
noncomputable def hp (q P : ℕ) : ℝ := lam * (Lp q : ℝ) - P

/-- `𝒫_P` (Definition 1.8): the words of length `P` with `L_p` 1s that survive from height 0. -/
noncomputable def Pset (q P : ℕ) : Finset (Fin P → Bool) := by
  classical
  exact univ.filter (fun w => ones w P = Lp q ∧ SurvW 0 w)

/-- `𝒯_{L,P}` (Definition 1.8): the words of length `t = s − P` whose first letter is 1, with `L − L_p` 1s, that survive from height `h_p`. -/
noncomputable def Tset (q s L P : ℕ) : Finset (Fin (s - P) → Bool) := by
  classical
  exact univ.filter (fun τ => (∀ h : 0 < s - P, τ ⟨0, h⟩ = true) ∧ ones τ (s - P) = L - Lp q ∧
    SurvW (hp q P) τ)

/-- The position `P` (counted from 0) of the `(L_p+1)`-th 1 of the word `u`; `n` if there is none. -/
noncomputable def slicePos {n : ℕ} (q : ℕ) (u : Fin n → Bool) : ℕ := by
  classical
  exact Nat.find (⟨n, Or.inl le_rfl⟩ : ∃ P, P ≥ n ∨ Lp q < ones u (P + 1))

/-- `R_δ` with the constants as parameters: the pairs `(L, P)` with `0 ≤ h_L ≤ bδ²q`, `0 < h_p ≤ aδq`, `𝒫_P ≠ ∅`, `𝒯_{L,P} ≠ ∅`.
Definition 1.10 of version 2 of the proof manuscript has `(a, b) = (1.23, 3.5)` (`Rdelta`); Definition 1.10 of version 3 (§4.2.1 of that manuscript) has
`(a, b) = (1.38, 4.48)` (Definition 3.12 of the paper, revision r7). -/
def RdeltaG (a b δ : ℝ) (s q : ℕ) (L P : ℕ) : Prop :=
  0 ≤ hL s L ∧ hL s L ≤ b * δ ^ 2 * q ∧ 0 < hp q P ∧ hp q P ≤ a * δ * q ∧
    (Pset q P).Nonempty ∧ (Tset q s L P).Nonempty ∧ P < s

/-- `R_δ` (Definition 1.10 of version 2; revision r6 of the paper): the pairs `(L, P)` with `0 ≤ h_L ≤ 3.5δ²q`, `0 < h_p ≤ 1.23δq`, `𝒫_P ≠ ∅`, `𝒯_{L,P} ≠ ∅`
(`RdeltaG` with `(a, b) = (1.23, 3.5)`). -/
def Rdelta (δ : ℝ) (s q : ℕ) (L P : ℕ) : Prop := RdeltaG 1.23 3.5 δ s q L P

end Collatz.M1
