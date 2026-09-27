import CollatzProof.M1.C_Words

/-!
# Auxiliary (2) for Theorem A: Fourier analysis on `ℤ/N` (orthogonality, and a Parseval-type identity for sums of autocorrelations)

The formula `r_E(v) = 2^{−q} Σ_ξ |Ê(ξ)|² e(vξ/2^q)` of §1.6 is proved in the form used in Lemma 3.2,
`2^q Σ_{τ,τ'} r_E(G(τ') − G(τ)) = Σ_ξ |Ê(ξ)|²|Ĝ(ξ)|²`.
-/

namespace Collatz.M1

open Finset

lemma C_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma C_eC_conj (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC; rw [← Complex.exp_conj]; congr 1
  simp [Complex.conj_ofReal, map_ofNat]

lemma C_eC_int (m : ℤ) : eC m = 1 := by
  unfold eC
  have : 2 * (Real.pi : ℂ) * Complex.I * (((m : ℝ)) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this]; exact Complex.exp_int_mul_two_pi_mul_I m

lemma C_eC_nat_mul (n : ℕ) (x : ℝ) : eC (n * x) = eC x ^ n := by
  unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- Orthogonality: `Σ_{ξ<N} e(ξk/N) = N·[N ∣ k]`. -/
lemma C_orth (N : ℕ) (hN : 0 < N) (k : ℤ) :
    ∑ ξ ∈ range N, eC ((ξ : ℝ) * k / N) = if (N : ℤ) ∣ k then (N : ℂ) else 0 := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hterm : ∀ ξ : ℕ, eC ((ξ : ℝ) * k / N) = eC ((k : ℝ) / N) ^ ξ := by
    intro ξ; rw [← C_eC_nat_mul]; congr 1; ring
  simp_rw [hterm]
  split_ifs with hd
  · obtain ⟨m, hm⟩ := hd
    have h1 : eC ((k : ℝ) / N) = 1 := by
      have : (k : ℝ) / N = ((m : ℤ) : ℝ) := by
        rw [hm]; push_cast; field_simp
      rw [this, C_eC_int]
    simp [h1]
  · have hne : eC ((k : ℝ) / N) ≠ 1 := by
      intro h
      unfold eC at h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      apply hd
      refine ⟨m, ?_⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : (((k : ℝ) / N : ℝ) : ℂ) = (m : ℂ) := by
        apply mul_left_cancel₀ hpi
        rw [hm]; ring
      have h3 : (k : ℝ) / N = (m : ℝ) := by exact_mod_cast h2
      have h4 : (k : ℝ) = (N : ℝ) * m := by
        field_simp at h3; linarith
      exact_mod_cast h4
    rw [geom_sum_eq hne]
    have : eC ((k : ℝ) / N) ^ N = 1 := by
      rw [← C_eC_nat_mul]
      have : (N : ℝ) * ((k : ℝ) / N) = ((k : ℤ) : ℝ) := by field_simp
      rw [this, C_eC_int]
    rw [this]; simp

/-- Expanding `z · conj z` as a double sum: `|Σ_a e(ξX_a/N)|² = Σ_{(a,a')} e(ξ(X_a − X_{a'})/N)`. -/
lemma C_sq_sum {α : Type*} (A : Finset α) (X : α → ℤ) (N : ℕ) (ξ : ℕ) :
    ((‖∑ a ∈ A, eC ((ξ : ℝ) * X a / N)‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ A ×ˢ A, eC ((ξ : ℝ) * (X p.1 - X p.2 : ℤ) / N) := by
  push_cast
  rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro a' _
  rw [C_eC_conj, ← C_eC_add]
  congr 1; push_cast; ring

/-- General form of the Parseval-type identity:
`Σ_{ξ<N} |Σ_a e(ξX_a/N)|² |Σ_b e(ξY_b/N)|² = N · #{(a,a',b,b') | N ∣ X_a − X_{a'} + Y_b − Y_{b'}}`. -/
lemma C_four_gen (N : ℕ) (hN : 0 < N) {α β : Type*} (A : Finset α) (B : Finset β)
    (X : α → ℤ) (Y : β → ℤ) :
    ∑ ξ ∈ range N, ‖∑ a ∈ A, eC ((ξ : ℝ) * X a / N)‖ ^ 2 * ‖∑ b ∈ B, eC ((ξ : ℝ) * Y b / N)‖ ^ 2 =
      N * (((A ×ˢ A) ×ˢ (B ×ˢ B)).filter
        (fun p => (N : ℤ) ∣ X p.1.1 - X p.1.2 + (Y p.2.1 - Y p.2.2))).card := by
  apply Complex.ofReal_injective
  push_cast
  have step : ∀ ξ ∈ range N,
      ((‖∑ a ∈ A, eC ((ξ : ℝ) * X a / N)‖ : ℂ)) ^ 2 * ((‖∑ b ∈ B, eC ((ξ : ℝ) * Y b / N)‖ : ℂ)) ^ 2 =
        ∑ p ∈ (A ×ˢ A) ×ˢ (B ×ˢ B),
          eC ((ξ : ℝ) * (X p.1.1 - X p.1.2 + (Y p.2.1 - Y p.2.2) : ℤ) / N) := by
    intro ξ _
    have h1 := C_sq_sum A X N ξ
    have h2 := C_sq_sum B Y N ξ
    push_cast at h1 h2
    rw [h1, h2, Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl; intro p _
    rw [← C_eC_add]; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  simp_rw [C_orth N hN]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `r_E(v) = #{(z, z') ∈ E² | 2^q ∣ z' − z − v}` (for `E ⊂ [0, 2^q)`, this is `#{z ∈ E | z + v mod 2^q ∈ E}`). -/
def C_rE (q : ℕ) (E : Finset ℕ) (v : ℤ) : ℕ :=
  ((E ×ˢ E).filter (fun p => (2 ^ q : ℤ) ∣ (p.2 : ℤ) - p.1 - v)).card

/-- The Fourier part of Lemma 3.2: `2^q Σ_{b,b'} r_E(G(b') − G(b)) = Σ_ξ |Ê(ξ)|² |Σ_b e(ξG(b)/2^q)|²`. -/
lemma C_fourier (q : ℕ) (E : Finset ℕ) {β : Type*} (B : Finset β) (G : β → ℤ) :
    (2 ^ q : ℝ) * ∑ b ∈ B, ∑ b' ∈ B, (C_rE q E (G b' - G b) : ℝ) =
      ∑ ξ ∈ range (2 ^ q), ‖Ehat q E ξ‖ ^ 2 * ‖∑ b ∈ B, eC ((ξ : ℝ) * (G b : ℝ) / 2 ^ q)‖ ^ 2 := by
  have hN : 0 < 2 ^ q := by positivity
  have hE : ∀ ξ : ℕ, Ehat q E ξ = ∑ z ∈ E, eC ((ξ : ℝ) * ((-(z : ℤ) : ℤ) : ℝ) / ((2 ^ q : ℕ) : ℝ)) := by
    intro ξ; unfold Ehat
    apply Finset.sum_congr rfl; intro z _
    congr 1; push_cast; ring
  have hG : ∀ ξ : ℕ, ∑ b ∈ B, eC ((ξ : ℝ) * (G b : ℝ) / 2 ^ q) =
      ∑ b ∈ B, eC ((ξ : ℝ) * (G b : ℝ) / ((2 ^ q : ℕ) : ℝ)) := by
    intro ξ; push_cast; rfl
  simp_rw [hE, hG]
  rw [C_four_gen (2 ^ q) hN E B (fun z => -(z : ℤ)) G]
  have hcard : (((E ×ˢ E) ×ˢ (B ×ˢ B)).filter
      (fun p => ((2 ^ q : ℕ) : ℤ) ∣ -(p.1.1 : ℤ) - -(p.1.2 : ℤ) + (G p.2.1 - G p.2.2))).card =
      ∑ b ∈ B, ∑ b' ∈ B, C_rE q E (G b' - G b) := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm, Finset.sum_product]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro b' _
    unfold C_rE
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl; intro p _
    have e : -(p.1 : ℤ) - -(p.2 : ℤ) + (G b - G b') = (p.2 : ℤ) - p.1 - (G b' - G b) := by ring
    simp only [Nat.cast_pow, Nat.cast_ofNat, e]
  rw [hcard]
  push_cast
  ring

end Collatz.M1
