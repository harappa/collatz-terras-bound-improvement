import CollatzProof.M1.D_Slice

/-!
# Auxiliary for Theorem B: indexing by the Chinese remainder theorem (§5.1) and the expansion of `Ĝ`

To `(ξ, η) ∈ [0, 2^q) × ℤ/3^L` we associate the representative `N(ξ, η) ∈ [−2^{q−1}3^L, 2^{q−1}3^L)` with `N ≡ ξ3^L − η2^q` (mod `2^q 3^L`).
Then `ξ_N = ξ` and `η_N := −2^{−q}N = η` (mod `3^L`), and the correspondence is injective.
The prefix `D_` marks auxiliary declarations for Theorem B.
-/

namespace Collatz.M1

open Finset

section CRT

variable (q L : ℕ)

/-- The CRT representative `N(ξ, η)`. -/
def D_Nrep (ξ : ℕ) (η : ZMod (3 ^ L)) : ℤ :=
  ((ξ : ℤ) * 3 ^ L - (η.val : ℤ) * 2 ^ q + 2 ^ (q - 1) * 3 ^ L) % (2 ^ q * 3 ^ L) -
    2 ^ (q - 1) * 3 ^ L

lemma D_two_pow_pred (hq : 1 ≤ q) : (2 : ℤ) ^ q = 2 * 2 ^ (q - 1) := by
  rw [← pow_succ']; congr 1; omega

lemma D_Nrep_bounds (hq : 1 ≤ q) (ξ : ℕ) (η : ZMod (3 ^ L)) :
    -((2 : ℤ) ^ (q - 1) * 3 ^ L) ≤ D_Nrep q L ξ η ∧ D_Nrep q L ξ η < 2 ^ (q - 1) * 3 ^ L := by
  unfold D_Nrep
  have hb : (0 : ℤ) < 2 ^ q * 3 ^ L := by positivity
  set X := (ξ : ℤ) * 3 ^ L - (η.val : ℤ) * 2 ^ q + 2 ^ (q - 1) * 3 ^ L
  have h1 := Int.emod_nonneg X (ne_of_gt hb)
  have h2 := Int.emod_lt_of_pos X hb
  have h3 : (2 : ℤ) ^ q * 3 ^ L = 2 * (2 ^ (q - 1) * 3 ^ L) := by
    rw [D_two_pow_pred q hq]; ring
  constructor <;> linarith

lemma D_Nrep_cong (ξ : ℕ) (η : ZMod (3 ^ L)) :
    ∃ m : ℤ, (ξ : ℤ) * 3 ^ L - (η.val : ℤ) * 2 ^ q = D_Nrep q L ξ η + 2 ^ q * 3 ^ L * m := by
  set X := (ξ : ℤ) * 3 ^ L - (η.val : ℤ) * 2 ^ q + 2 ^ (q - 1) * 3 ^ L with hX
  refine ⟨X / (2 ^ q * 3 ^ L), ?_⟩
  unfold D_Nrep
  rw [← hX]
  have := Int.emod_add_mul_ediv X (2 ^ q * 3 ^ L)
  linarith

lemma D_Nrep_modM (ξ : ℕ) (η : ZMod (3 ^ L)) :
    ((D_Nrep q L ξ η : ℤ) : ZMod (3 ^ L)) = -(η * 2 ^ q) := by
  obtain ⟨m, hm⟩ := D_Nrep_cong q L ξ η
  have h := congrArg (fun x : ℤ => (x : ZMod (3 ^ L))) hm
  push_cast at h
  rw [D_three_pow_eq_zero, ZMod.natCast_zmod_val] at h
  linear_combination -h

lemma D_isUnit_three (q L : ℕ) : IsUnit ((3 : ZMod (2 ^ q)) ^ L) := by
  have h := (ZMod.isUnit_iff_coprime 3 (2 ^ q)).mpr (Nat.Coprime.pow_right q (by norm_num))
  exact (by exact_mod_cast h : IsUnit (3 : ZMod (2 ^ q))).pow L

lemma D_xiN_Nrep {ξ : ℕ} (hξ : ξ < 2 ^ q) (η : ZMod (3 ^ L)) : xiN q L (D_Nrep q L ξ η) = ξ := by
  obtain ⟨m, hm⟩ := D_Nrep_cong q L ξ η
  have h := congrArg (fun x : ℤ => (x : ZMod (2 ^ q))) hm
  push_cast at h
  have e2 : (2 : ZMod (2 ^ q)) ^ q = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ q)
  rw [e2] at h
  have hN : ((D_Nrep q L ξ η : ℤ) : ZMod (2 ^ q)) = (ξ : ZMod (2 ^ q)) * 3 ^ L := by
    linear_combination -h
  unfold xiN
  rw [hN, mul_assoc, ZMod.mul_inv_of_unit _ (D_isUnit_three q L), mul_one, ZMod.val_cast_of_lt hξ]

lemma D_Nrep_inj :
    Set.InjOn (fun p : ℕ × ZMod (3 ^ L) => D_Nrep q L p.1 p.2)
      ((range (2 ^ q) ×ˢ (univ : Finset (ZMod (3 ^ L))) : Finset (ℕ × ZMod (3 ^ L))) : Set _) := by
  rintro ⟨ξ, η⟩ h ⟨ξ', η'⟩ h' heq
  simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at h h'
  simp only at heq
  have e1 : ξ = ξ' := by
    rw [← D_xiN_Nrep q L h.1 η, ← D_xiN_Nrep q L h'.1 η', heq]
  subst e1
  have e2 := D_Nrep_modM q L ξ η
  rw [heq, D_Nrep_modM q L ξ η'] at e2
  have hu : IsUnit ((2 : ZMod (3 ^ L)) ^ q) := (D_isUnit_two L).pow q
  have : η' * 2 ^ q = η * 2 ^ q := by linear_combination -e2
  rw [hu.mul_left_inj] at this
  rw [this]

end CRT

/-! ## Expansion of `Ĝ` (Lemmas 5.1 and 3.3) -/

section Expand

variable {q s L P : ℕ}

/-- The Syracuse characteristic function of the tails, `S(η) = Σ_τ ψ(η G(τ))` (`G ≡ 2^{−t}c_τ`, mod `3^L`). -/
noncomputable def D_S (q s L P : ℕ) (η : ZMod (3 ^ L)) : ℂ :=
  ∑ τ ∈ Tset q s L P, ZMod.stdAddChar (η * ((Gstat q s L P τ : ℤ) : ZMod (3 ^ L)))

/-- Lemma 5.1: `Ĝ(ξ) = e(−ξ3^L/2^q) Σ_η ω_ξ(η) S(η)`. -/
lemma D_Ghat_eq (hLp : Lp q ≤ L) (ht : 0 < s - P) (h2t : 2 ^ (s - P) < 3 ^ Lp q) (ξ : ℤ) :
    Ghat q s L P ξ = eC (-(ξ : ℝ) * 3 ^ L / 2 ^ q) *
      ∑ η : ZMod (3 ^ L), D_omega q L ξ η * D_S q s L P η := by
  unfold Ghat D_S
  have hτ : ∀ τ ∈ Tset q s L P, eC ((ξ : ℝ) * (Gstat q s L P τ : ℝ) / 2 ^ q) =
      eC (-(ξ : ℝ) * 3 ^ L / 2 ^ q) * ∑ η : ZMod (3 ^ L), D_omega q L ξ η *
        ZMod.stdAddChar (η * ((Gstat q s L P τ : ℤ) : ZMod (3 ^ L))) := by
    intro τ hτ
    obtain ⟨hr1, hr2⟩ := D_G_range hτ hLp ht h2t
    set G := Gstat q s L P τ
    have hexp := D_expand q L ξ (G + 3 ^ L) (by linarith) (by linarith)
    have hcast : ((G + 3 ^ L : ℤ) : ZMod (3 ^ L)) = ((G : ℤ) : ZMod (3 ^ L)) := by
      push_cast; rw [D_three_pow_eq_zero, add_zero]
    rw [hcast] at hexp
    rw [← hexp, ← D_eC_add]
    congr 1; push_cast; ring
  rw [sum_congr rfl hτ, ← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl; intro η _
  rw [mul_sum]

lemma D_Ghat_sq (hLp : Lp q ≤ L) (ht : 0 < s - P) (h2t : 2 ^ (s - P) < 3 ^ Lp q) (ξ : ℤ) :
    ‖Ghat q s L P ξ‖ ^ 2 ≤ (∑ η : ZMod (3 ^ L), ‖D_omega q L ξ η‖) *
      ∑ η : ZMod (3 ^ L), ‖D_omega q L ξ η‖ * ‖D_S q s L P η‖ ^ 2 := by
  rw [D_Ghat_eq hLp ht h2t ξ, norm_mul, D_norm_eC, one_mul]
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  simp_rw [norm_mul]
  -- `sum_sq_le_sum_mul_sum_of_sq_le_mul` exists only in v4.34. Use the equality version, which exists in both versions (deprecation warning in v4.34)
  apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro i _; exact norm_nonneg _
  · intro i _; positivity
  · intro i _; ring

end Expand

end Collatz.M1
