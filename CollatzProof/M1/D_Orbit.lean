import Mathlib

/-!
# Auxiliary for Theorem B: averaging over swap orbits (abstract form of Lemma 5.3 (iii))

Suppose that on a finite set `T` there is, for each element `τ` and each subset `U ⊆ B(τ)`, an involution `flip U` preserving `B`.
If `f(flip U τ) = f(τ) Π_{k∈U} z_τ(k)` and `|f| = 1`, then `|Σ_τ f(τ)|² ≤ |T| Σ_τ Π_{k∈B(τ)} |(1 + z_τ(k))/2|²`.
(The elements of an orbit `O` are obtained by the swaps `U ⊆ B_O`, and `|O| = 2^{|B_O|}`. Instead of writing the orbit sums explicitly, we write the average over `U` at each tail.)
The prefix `D_` marks auxiliary declarations for Theorem B.
-/

namespace Collatz.M1

open Finset

/-- The swap-averaging identity: `Σ_τ f(τ) = Σ_τ 2^{−|B(τ)|} Σ_{U ⊆ B(τ)} f(flip U τ)`. -/
lemma D_orbit_avg {α : Type*} (T : Finset α) (B : α → Finset ℕ) (Ω : Finset ℕ)
    (flip : Finset ℕ → α → α) (hBΩ : ∀ τ ∈ T, B τ ⊆ Ω)
    (hT : ∀ τ ∈ T, ∀ U ⊆ B τ, flip U τ ∈ T)
    (hB : ∀ τ ∈ T, ∀ U ⊆ B τ, B (flip U τ) = B τ)
    (hinv : ∀ τ ∈ T, ∀ U ⊆ B τ, flip U (flip U τ) = τ) (f : α → ℂ) :
    ∑ τ ∈ T, f τ = ∑ τ ∈ T, ((2 : ℂ) ^ (B τ).card)⁻¹ * ∑ U ∈ (B τ).powerset, f (flip U τ) := by
  classical
  set c : α → ℂ := fun τ => ((2 : ℂ) ^ (B τ).card)⁻¹ with hc
  -- write `U ⊆ B τ` via an indicator function on the subsets of `Ω`
  have hpow : ∀ τ ∈ T, ∀ g : Finset ℕ → ℂ,
      ∑ U ∈ (B τ).powerset, g U = ∑ U ∈ Ω.powerset, if U ⊆ B τ then g U else 0 := by
    intro τ hτ g
    rw [← sum_filter]
    congr 1
    ext U; simp only [mem_powerset, mem_filter]
    constructor
    · intro h; exact ⟨h.trans (hBΩ τ hτ), h⟩
    · intro h; exact h.2
  have step : ∀ U ∈ Ω.powerset,
      ∑ τ ∈ T, (if U ⊆ B τ then c τ * f (flip U τ) else 0) =
        ∑ τ ∈ T, (if U ⊆ B τ then c τ * f τ else 0) := by
    intro U _
    rw [← sum_filter, ← sum_filter]
    apply sum_nbij' (flip U) (flip U)
    · intro τ hτ
      simp only [mem_filter] at hτ ⊢
      exact ⟨hT τ hτ.1 U hτ.2, by rw [hB τ hτ.1 U hτ.2]; exact hτ.2⟩
    · intro τ hτ
      simp only [mem_filter] at hτ ⊢
      exact ⟨hT τ hτ.1 U hτ.2, by rw [hB τ hτ.1 U hτ.2]; exact hτ.2⟩
    · intro τ hτ; simp only [mem_filter] at hτ; exact hinv τ hτ.1 U hτ.2
    · intro τ hτ; simp only [mem_filter] at hτ; exact hinv τ hτ.1 U hτ.2
    · intro τ hτ
      simp only [mem_filter] at hτ
      simp only [hc, hB τ hτ.1 U hτ.2]
  calc ∑ τ ∈ T, f τ = ∑ τ ∈ T, c τ * ∑ U ∈ (B τ).powerset, f τ := by
        apply sum_congr rfl; intro τ _
        rw [sum_const, card_powerset, nsmul_eq_mul, hc]
        push_cast
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
    _ = ∑ τ ∈ T, ∑ U ∈ Ω.powerset, (if U ⊆ B τ then c τ * f τ else 0) := by
        apply sum_congr rfl; intro τ hτ
        rw [mul_sum, hpow τ hτ]
    _ = ∑ U ∈ Ω.powerset, ∑ τ ∈ T, (if U ⊆ B τ then c τ * f τ else 0) := sum_comm
    _ = ∑ U ∈ Ω.powerset, ∑ τ ∈ T, (if U ⊆ B τ then c τ * f (flip U τ) else 0) :=
        (sum_congr rfl step).symm
    _ = ∑ τ ∈ T, ∑ U ∈ Ω.powerset, (if U ⊆ B τ then c τ * f (flip U τ) else 0) := sum_comm
    _ = ∑ τ ∈ T, c τ * ∑ U ∈ (B τ).powerset, f (flip U τ) := by
        apply sum_congr rfl; intro τ hτ
        rw [mul_sum, hpow τ hτ]

/-- Abstract form of Lemma 5.3 (iii). -/
lemma D_orbit_bound {α : Type*} (T : Finset α) (B : α → Finset ℕ) (Ω : Finset ℕ)
    (flip : Finset ℕ → α → α) (hBΩ : ∀ τ ∈ T, B τ ⊆ Ω)
    (hT : ∀ τ ∈ T, ∀ U ⊆ B τ, flip U τ ∈ T)
    (hB : ∀ τ ∈ T, ∀ U ⊆ B τ, B (flip U τ) = B τ)
    (hinv : ∀ τ ∈ T, ∀ U ⊆ B τ, flip U (flip U τ) = τ) (f : α → ℂ) (z : α → ℕ → ℂ)
    (hf : ∀ τ ∈ T, ∀ U ⊆ B τ, f (flip U τ) = f τ * ∏ k ∈ U, z τ k)
    (hnorm : ∀ τ ∈ T, ‖f τ‖ = 1) :
    ‖∑ τ ∈ T, f τ‖ ^ 2 ≤ T.card * ∑ τ ∈ T, ∏ k ∈ B τ, ‖(1 + z τ k) / 2‖ ^ 2 := by
  rw [D_orbit_avg T B Ω flip hBΩ hT hB hinv f]
  have hg : ∀ τ ∈ T, ((2 : ℂ) ^ (B τ).card)⁻¹ * ∑ U ∈ (B τ).powerset, f (flip U τ) =
      f τ * ∏ k ∈ B τ, ((1 + z τ k) / 2) := by
    intro τ hτ
    rw [sum_congr rfl (fun U hU => hf τ hτ U (mem_powerset.mp hU)), ← mul_sum, ← prod_one_add,
      prod_div_distrib, prod_const]
    ring
  rw [sum_congr rfl hg]
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  gcongr with τ hτ
  rw [norm_mul, hnorm τ hτ, one_mul, norm_prod, ← prod_pow]

end Collatz.M1
