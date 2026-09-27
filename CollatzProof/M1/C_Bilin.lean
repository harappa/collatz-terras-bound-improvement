import CollatzProof.M1.C_Fourier

/-!
# Auxiliary (3) for Theorem A: abstract form of the bilinear inequality (Lemma 3.2)

For a set `A` of first-half words (`κ : A → [0, K)`, multiplicity `≤ m`) and a set `B` of tails (with an integer-valued statistic `G`),
the sum of `M_e(k) = #{b ∈ B | (G(b) + c₁(k + eD)) mod 2^q ∈ E}` is bounded by Cauchy–Schwarz, multiplicity, and Parseval.
Lemma 3.2 of the manuscript counts the terms with `τ = τ'` separately by `|𝒯||E|`; here the diagonal terms are also included in the Fourier sum
(since `r_E ≥ 0` the same upper bound holds, and the first term is not needed).
-/

namespace Collatz.M1

open Finset

/-- `M_e(k) = #{b ∈ B | (G(b) + c₁(k + eD)) mod 2^q ∈ E}`. -/
noncomputable def C_M (q : ℕ) (E : Finset ℕ) {β : Type*} (B : Finset β) (G : β → ℤ) (c1 D : ℤ)
    (e k : ℕ) : ℕ := by
  classical
  exact (B.filter (fun b => ((G b + c1 * ((k : ℤ) + e * D)) % 2 ^ q).toNat ∈ E)).card

/-- Congruence modulo `2^q` of `(x mod 2^q).toNat`. -/
lemma C_toNat_emod (q : ℕ) (x : ℤ) : (((x % 2 ^ q).toNat : ℕ) : ℤ) = x % 2 ^ q := by
  apply Int.toNat_of_nonneg
  apply Int.emod_nonneg; positivity

lemma C_dvd_sub_emod (N x : ℤ) : N ∣ x - x % N := by
  rw [Int.emod_def]; simp

/-- For a single pair `(b, b')`: `#{k < K | Z_k(b) ∈ E ∧ Z_k(b') ∈ E} ≤ r_E(G(b') − G(b))`. -/
lemma C_pair_le (q : ℕ) (E : Finset ℕ) (K : ℕ) (hK : K ≤ 2 ^ q) (c1 D : ℤ)
    (hc1 : IsCoprime (2 ^ q : ℤ) c1) (e : ℕ) (x x' : ℤ) :
    ((range K).filter (fun k : ℕ => ((x + c1 * ((k : ℤ) + e * D)) % 2 ^ q).toNat ∈ E ∧
        ((x' + c1 * ((k : ℤ) + e * D)) % 2 ^ q).toNat ∈ E)).card ≤ C_rE q E (x' - x) := by
  unfold C_rE
  apply Finset.card_le_card_of_injOn
    (fun k : ℕ => (((x + c1 * ((k : ℤ) + e * D)) % 2 ^ q).toNat,
      ((x' + c1 * ((k : ℤ) + e * D)) % 2 ^ q).toNat))
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter] at hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hk.2.1, hk.2.2⟩, ?_⟩
    rw [C_toNat_emod, C_toNat_emod]
    have h1 := C_dvd_sub_emod (2 ^ q) (x + c1 * ((k : ℤ) + e * D))
    have h2 := C_dvd_sub_emod (2 ^ q) (x' + c1 * ((k : ℤ) + e * D))
    have : (x' + c1 * ((k : ℤ) + e * D)) % 2 ^ q - (x + c1 * ((k : ℤ) + e * D)) % 2 ^ q - (x' - x) =
        (x + c1 * ((k : ℤ) + e * D) - (x + c1 * ((k : ℤ) + e * D)) % 2 ^ q) -
          (x' + c1 * ((k : ℤ) + e * D) - (x' + c1 * ((k : ℤ) + e * D)) % 2 ^ q) := by ring
    rw [this]; exact dvd_sub h1 h2
  · intro k hk k' hk' heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk hk'
    simp only [Prod.mk.injEq] at heq
    have h0 := heq.1
    have h1 : (x + c1 * ((k : ℤ) + e * D)) % 2 ^ q = (x + c1 * ((k' : ℤ) + e * D)) % 2 ^ q := by
      have := congrArg (fun n : ℕ => (n : ℤ)) h0
      simpa only [C_toNat_emod] using this
    have h2 : (2 ^ q : ℤ) ∣ c1 * ((k : ℤ) - k') := by
      have := Int.ModEq.dvd h1.symm
      have e2 : x + c1 * ((k : ℤ) + e * D) - (x + c1 * ((k' : ℤ) + e * D)) = c1 * ((k : ℤ) - k') := by ring
      rw [e2] at this; exact this
    have h3 : (2 ^ q : ℤ) ∣ (k : ℤ) - k' := hc1.dvd_of_dvd_mul_left h2
    have hk1 : (k : ℤ) < 2 ^ q := by exact_mod_cast (lt_of_lt_of_le hk.1 hK : k < 2 ^ q)
    have hk2 : (k' : ℤ) < 2 ^ q := by exact_mod_cast (lt_of_lt_of_le hk'.1 hK : k' < 2 ^ q)
    have := Int.eq_of_sub_eq_zero (Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega))
    exact_mod_cast this

/-- Abstract form of Lemma 3.2 (with the diagonal included in the Fourier sum):
`(Σ_{e<2} Σ_{a∈A} M_e(κ(a)))² ≤ 4|A| m 2^{−q} Σ_ξ |Ê(ξ)|² |Σ_b e(ξG(b)/2^q)|²`. -/
lemma C_bilin_abstract (q : ℕ) (E : Finset ℕ) {α β : Type*} (A : Finset α) (κ : α → ℕ)
    (K m : ℕ) (hK : K ≤ 2 ^ q) (hκ : ∀ a ∈ A, κ a < K)
    (hm : ∀ k, (A.filter (fun a => κ a = k)).card ≤ m)
    (B : Finset β) (G : β → ℤ) (c1 D : ℤ) (hc1 : IsCoprime (2 ^ q : ℤ) c1) :
    ((∑ e ∈ range 2, ∑ a ∈ A, C_M q E B G c1 D e (κ a) : ℕ) : ℝ) ^ 2 ≤
      4 * A.card * m / 2 ^ q *
        ∑ ξ ∈ range (2 ^ q), ‖Ehat q E ξ‖ ^ 2 * ‖∑ b ∈ B, eC ((ξ : ℝ) * (G b : ℝ) / 2 ^ q)‖ ^ 2 := by
  classical
  rw [← C_fourier q E B G]
  set R : ℝ := ∑ b ∈ B, ∑ b' ∈ B, (C_rE q E (G b' - G b) : ℝ) with hR
  -- (c): `Σ_{k<K} M_e(k)² ≤ R`
  have hc : ∀ e : ℕ, ∑ k ∈ range K, ((C_M q E B G c1 D e k : ℕ) : ℝ) ^ 2 ≤ R := by
    intro e
    have hsq : ∀ k : ℕ, ((C_M q E B G c1 D e k : ℕ) : ℝ) ^ 2 =
        ∑ b ∈ B, ∑ b' ∈ B,
          (if ((G b + c1 * ((k : ℤ) + e * D)) % 2 ^ q).toNat ∈ E ∧
              ((G b' + c1 * ((k : ℤ) + e * D)) % 2 ^ q).toNat ∈ E then (1:ℝ) else 0) := by
      intro k
      unfold C_M
      rw [Finset.card_filter]
      push_cast
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro b' _
      split_ifs <;> simp_all
    simp_rw [hsq]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro b' _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast C_pair_le q E K hK c1 D hc1 e (G b) (G b')
  -- (b): multiplicity
  have hb : ∀ e : ℕ, ∑ a ∈ A, ((C_M q E B G c1 D e (κ a) : ℕ) : ℝ) ^ 2 ≤
      m * ∑ k ∈ range K, ((C_M q E B G c1 D e k : ℕ) : ℝ) ^ 2 := by
    intro e
    rw [← Finset.sum_fiberwise_of_maps_to' (s := A) (t := range K) (g := κ)
      (fun a ha => Finset.mem_range.2 (hκ a ha)) (fun k => ((C_M q E B G c1 D e k : ℕ) : ℝ) ^ 2)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k _
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast hm k
  -- (a): Cauchy–Schwarz
  have ha : ((∑ e ∈ range 2, ∑ a ∈ A, C_M q E B G c1 D e (κ a) : ℕ) : ℝ) ^ 2 ≤
      (2 * A.card) * ∑ e ∈ range 2, ∑ a ∈ A, ((C_M q E B G c1 D e (κ a) : ℕ) : ℝ) ^ 2 := by
    push_cast
    rw [← Finset.sum_product', ← Finset.sum_product']
    have := sq_sum_le_card_mul_sum_sq (s := range 2 ×ˢ A)
      (f := fun p : ℕ × α => ((C_M q E B G c1 D p.1 (κ p.2) : ℕ) : ℝ))
    simpa [Finset.card_product] using this
  have hR0 : 0 ≤ R := by positivity
  calc ((∑ e ∈ range 2, ∑ a ∈ A, C_M q E B G c1 D e (κ a) : ℕ) : ℝ) ^ 2
      ≤ (2 * A.card) * ∑ e ∈ range 2, ∑ a ∈ A, ((C_M q E B G c1 D e (κ a) : ℕ) : ℝ) ^ 2 := ha
    _ ≤ (2 * A.card) * ∑ e ∈ range 2, (m * R) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro e _
        exact (hb e).trans (mul_le_mul_of_nonneg_left (hc e) (by positivity))
    _ = 4 * A.card * m / 2 ^ q * (2 ^ q * R) := by
        rw [Finset.sum_const, Finset.card_range]
        field_simp
        ring

end Collatz.M1
