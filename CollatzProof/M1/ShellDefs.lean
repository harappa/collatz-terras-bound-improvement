import CollatzProof.M1.Fourier

/-!
# Definitions of §5–§7: swap blocks, phases, shells, shell averages, depth of a frequency

Slice `(L, P)`, `t = s − P`, tail `τ : Fin t → Bool`.
- Block `k` (`1 ≤ k`, `2k < t`) is the pair of positions `(2k−1, 2k)`. A swap block contains exactly one 1, and the height just before it (at time `2k−1`, starting from `h_p`) is at least 1 (Definition 5.2).
- `ℓ_b = 2k−1`, `j_b = o_{2k−1}(τ) + 1`, `n_b = L_p + j_b`, `d_b = t − ℓ_b`, `e_b = L − n_b`.
- The shell average `A_k` is the orbit sum `Σ_O (|O|/|𝒯|)⟨Π_{b∈ℬ_O} cos² πθ_b⟩_k` of Definition 5.4, rewritten, using that ℬ is constant on orbits (Lemma 5.3 (i)),
  as the tail average `(1/|𝒯|) Σ_τ ⟨Π_{b∈ℬ(τ)} cos² πθ_b⟩_k` (equivalent; shown by Lemma 5.3 (i)).
-/

namespace Collatz.M1

open Finset

variable (q s L P : ℕ)

/-- Block `k` is a swap block of the tail `τ` (Definition 5.2). -/
def IsSwap (τ : Fin (s - P) → Bool) (k : ℕ) : Prop :=
  ∃ h : 2 * k < s - P, 1 ≤ k ∧
    τ ⟨2 * k - 1, by omega⟩ ≠ τ ⟨2 * k, h⟩ ∧ 1 ≤ hw (hp q P) τ (2 * k - 1)

/-- The set `ℬ(τ)` of swap blocks (as a set of block indices `k`). -/
noncomputable def Bset (τ : Fin (s - P) → Bool) : Finset ℕ := by
  classical
  exact (range (s - P)).filter (fun k => IsSwap q s P τ k)

/-- `j_b = o_{2k−1}(τ) + 1` (the 1 in the block is the `j_b`-th 1 of the tail). -/
def jb (τ : Fin (s - P) → Bool) (k : ℕ) : ℕ := ones τ (2 * k - 1) + 1

/-- `n_b = L_p + j_b`. -/
def nb (τ : Fin (s - P) → Bool) (k : ℕ) : ℕ := Lp q + jb s P τ k

/-- `d_b = t − ℓ_b = t − (2k − 1)`. -/
def db (k : ℕ) : ℕ := (s - P) - (2 * k - 1)

/-- Phase `θ_b(N) = ⟨−N 2^{ℓ_b − t − q}⟩_{3^{n_b}}/3^{n_b}` (Lemma 5.3 (ii)). `2^{ℓ_b−t−q} = (2^{d_b+q})^{−1}` is taken modulo `3^{n_b}`. -/
noncomputable def theta (τ : Fin (s - P) → Bool) (k : ℕ) (N : ℤ) : ℝ :=
  (inv2mod (db s P k + q) (nb q s P τ k) (-N) : ℝ) / 3 ^ (nb q s P τ k)

/-- Shell `J_k` (Definition 5.4). -/
noncomputable def shell (k : ℕ) : Finset ℤ :=
  if k = 0 then Ico (-(2 ^ (q - 1) : ℤ)) (2 ^ (q - 1))
  else Ico ((2 ^ (q - 1) : ℤ) * 3 ^ (k - 1)) (2 ^ (q - 1) * 3 ^ k) ∪
    Ico (-((2 ^ (q - 1) : ℤ) * 3 ^ k)) (-((2 ^ (q - 1) : ℤ) * 3 ^ (k - 1)))

/-- `ξ_N = ⟨3^{−L}N⟩_{2^q} ∈ [0, 2^q)`. -/
noncomputable def xiN (N : ℤ) : ℕ := ((N : ZMod (2 ^ q)) * ((3 : ZMod (2 ^ q)) ^ L)⁻¹).val

/-- Weight `w(N) = |Ê(ξ_N)|² 1[ξ_N ≠ 0]` (`E = E_L`). -/
noncomputable def wN (N : ℤ) : ℝ :=
  if xiN q L N = 0 then 0 else ‖Ehat q (Eset q (hL s L)) (xiN q L N)‖ ^ 2

/-- Shell average `⟨F⟩_k = Σ_{N∈J_k} w(N)F(N) / Σ_{N∈J_k} w(N)`. -/
noncomputable def shAvg (k : ℕ) (F : ℤ → ℝ) : ℝ :=
  (∑ N ∈ shell q k, wN q s L N * F N) / ∑ N ∈ shell q k, wN q s L N

/-- Riesz product over the swap blocks `Π_{b∈ℬ(τ)} cos² πθ_b(N)`. -/
noncomputable def riesz (τ : Fin (s - P) → Bool) (N : ℤ) : ℝ :=
  ∏ k ∈ Bset q s P τ, Real.cos (Real.pi * theta q s P τ k N) ^ 2

/-- Shell average `A_k` (Definition 5.4, in the form of a tail average). -/
noncomputable def Ak (k : ℕ) : ℝ :=
  (∑ τ ∈ Tset q s L P, shAvg q s L k (riesz q s P τ)) / (Tset q s L P).card

/-- Depth of a frequency `dep(ξ) = q − v₂(ξ)` (`ξ ≠ 0`), `dep(0) = 0` (Definition 7.1). -/
noncomputable def dep (ξ : ℕ) : ℕ := if ξ % 2 ^ q = 0 then 0 else q - padicValNat 2 (ξ % 2 ^ q)

/-- `ϖ_j = W^{−1} Σ_{ξ≠0, dep(ξ)≤j} |Ê(ξ)|²` (Definition 7.1, `E = E_L`). -/
noncomputable def varpi (j : ℕ) : ℝ :=
  (∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => dep q ξ ≤ j),
      ‖Ehat q (Eset q (hL s L)) ξ‖ ^ 2) / Wsum q (Eset q (hL s L))

/-- Shell average `⟨F⟩^{>j}_k` restricted to depth `> j` (same denominator). -/
noncomputable def shAvgDeep (k j : ℕ) (F : ℤ → ℝ) : ℝ :=
  (∑ N ∈ (shell q k).filter (fun N => j < dep q (xiN q L N)), wN q s L N * F N) /
    ∑ N ∈ shell q k, wN q s L N

/-- `A_k^{>j}` (Definition 7.1). -/
noncomputable def AkDeep (k j : ℕ) : ℝ :=
  (∑ τ ∈ Tset q s L P, shAvgDeep q s L k j (riesz q s P τ)) / (Tset q s L P).card

/-- `N_d(τ)`: the number of swap blocks within distance `d` of the end (`d_b ≤ d`) (§6). -/
noncomputable def Nd (τ : Fin (s - P) → Bool) (d : ℕ) : ℕ := by
  classical
  exact ((Bset q s P τ).filter (fun k => db s P k ≤ d)).card

/-- Average over tails `𝔼_{τ∈𝒯} g(N_d(τ))`. -/
noncomputable def ETail (d : ℕ) (g : ℕ → ℝ) : ℝ :=
  (∑ τ ∈ Tset q s L P, g (Nd q s P τ d)) / (Tset q s L P).card

end Collatz.M1
