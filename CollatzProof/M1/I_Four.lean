import CollatzProof.M1.I_Kernel
import CollatzProof.M1.DeepDefs

/-!
# Auxiliary results for §11 and §12: Fourier identities

- Depth of a frequency: if `ξ < 2^q` and `j₀ ≤ q`, then `dep(ξ) ≤ j₀ ↔ 2^{q−j₀} ∣ ξ`.
- `|Ê(ξ)|² = Σ_{z,z'∈E} e(ξ(z'−z)/2^q)`, and the expansion of sums over a set of frequencies.
- `r^{deep}(v) = r_E(v) − r^{sh}(v)` (the form of Lemma 12.1 (ii); `I_rDeep_le`), Parseval `W = 2^q|E| − |E|²`.
- `‖Σ_ξ μ(ξ)e(vξ/2^q)‖ ≤ (2/(1−ϖ_{j₀}))ϱ_E(v)` (the second half of Lemma 11.2, `I_mu_sum_le`).
-/

namespace Collatz.M1

open Finset

/-! ## Depth of a frequency -/

lemma I_dep_zero (q : ℕ) : dep q 0 = 0 := by unfold dep; simp

lemma I_dep_le_iff (q j0 ξ : ℕ) (hξ : ξ < 2 ^ q) :
    dep q ξ ≤ j0 ↔ 2 ^ (q - j0) ∣ ξ := by
  unfold dep
  rw [Nat.mod_eq_of_lt hξ]
  by_cases h0 : ξ = 0
  · subst h0; simp
  · rw [if_neg h0, padicValNat_dvd_iff_le h0]
    omega

/-- `Σ_{ξ<2^q} e(ξm/2^q) = 2^q·1[2^q ∣ m]`. -/
lemma I_sum_eC_pow (q : ℕ) (m : ℤ) :
    ∑ ξ ∈ range (2 ^ q), eC ((ξ : ℝ) * m / 2 ^ q) = if (2 : ℤ) ^ q ∣ m then (2 : ℂ) ^ q else 0 := by
  have := I_sum_eC_range (2 ^ q) (by positivity) m
  push_cast at this
  exact this

/-- Sum over shallow frequencies: `Σ_{ξ<2^q, dep(ξ)≤j₀} e(ξm/2^q) = 2^{j₀}·1[2^{j₀} ∣ m]`. -/
lemma I_sum_shallow (q j0 : ℕ) (hj0 : j0 ≤ q) (m : ℤ) :
    ∑ ξ ∈ (range (2 ^ q)).filter (fun ξ => dep q ξ ≤ j0), eC ((ξ : ℝ) * m / 2 ^ q) =
      if (2 : ℤ) ^ j0 ∣ m then (2 : ℂ) ^ j0 else 0 := by
  have hset : (range (2 ^ q)).filter (fun ξ => dep q ξ ≤ j0) =
      (range (2 ^ j0)).image (fun μ => 2 ^ (q - j0) * μ) := by
    ext ξ
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hξ, hd⟩
      rw [I_dep_le_iff q j0 ξ hξ] at hd
      obtain ⟨μ, rfl⟩ := hd
      refine ⟨μ, ?_, rfl⟩
      have : 2 ^ (q - j0) * μ < 2 ^ (q - j0) * 2 ^ j0 := by
        rw [← pow_add, Nat.sub_add_cancel hj0]; exact hξ
      exact Nat.lt_of_mul_lt_mul_left this
    · rintro ⟨μ, hμ, rfl⟩
      have hlt : 2 ^ (q - j0) * μ < 2 ^ q := by
        calc 2 ^ (q - j0) * μ < 2 ^ (q - j0) * 2 ^ j0 := Nat.mul_lt_mul_of_pos_left hμ (by positivity)
          _ = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hj0]
      exact ⟨hlt, (I_dep_le_iff q j0 _ hlt).mpr (dvd_mul_right _ _)⟩
  rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by positivity) h)]
  have := I_sum_eC_pow j0 m
  rw [← this]
  apply sum_congr rfl; intro μ _
  congr 1
  push_cast
  rw [show (2 : ℝ) ^ q = 2 ^ (q - j0) * 2 ^ j0 by rw [← pow_add, Nat.sub_add_cancel hj0]]
  field_simp

/-! ## Expansion of `|Ê|²` -/

lemma I_normsq_Ehat (q : ℕ) (E : Finset ℕ) (ξ : ℕ) :
    ((‖Ehat q E ξ‖ : ℂ) ^ 2) =
      ∑ z ∈ E, ∑ z' ∈ E, eC ((ξ : ℝ) * (((z' : ℤ) - z : ℤ) : ℝ) / 2 ^ q) := by
  rw [← Complex.mul_conj']
  unfold Ehat
  rw [map_sum, sum_mul_sum]
  apply sum_congr rfl; intro z _; apply sum_congr rfl; intro z' _
  rw [I_conj_eC, ← I_eC_add]
  congr 1; push_cast; ring

/-- Expansion of a sum over a set `S` of frequencies. -/
lemma I_corr_expand (q : ℕ) (E S : Finset ℕ) (v : ℤ) :
    ∑ ξ ∈ S, (‖Ehat q E ξ‖ : ℂ) ^ 2 * eC ((v : ℝ) * ξ / 2 ^ q) =
      ∑ z ∈ E, ∑ z' ∈ E, ∑ ξ ∈ S, eC ((ξ : ℝ) * (((z' : ℤ) - z + v : ℤ) : ℝ) / 2 ^ q) := by
  simp_rw [I_normsq_Ehat, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro z _
  rw [sum_comm]
  apply sum_congr rfl; intro z' _
  apply sum_congr rfl; intro ξ _
  rw [← I_eC_add]; congr 1; push_cast; ring

/-! ## `r^{deep} = r_E − r^{sh}` -/

/-- Sum over deep frequencies = total sum − sum over shallow frequencies. -/
lemma I_deep_split (q j0 : ℕ) (f : ℕ → ℂ) :
    ∑ ξ ∈ ((range (2 ^ q)).erase 0).filter (fun ξ => j0 < dep q ξ), f ξ =
      ∑ ξ ∈ range (2 ^ q), f ξ - ∑ ξ ∈ (range (2 ^ q)).filter (fun ξ => dep q ξ ≤ j0), f ξ := by
  have hset : ((range (2 ^ q)).erase 0).filter (fun ξ => j0 < dep q ξ) =
      (range (2 ^ q)).filter (fun ξ => ¬ dep q ξ ≤ j0) := by
    ext ξ
    simp only [mem_filter, mem_erase, mem_range, not_le]
    constructor
    · rintro ⟨⟨_, h⟩, hd⟩; exact ⟨h, hd⟩
    · rintro ⟨h, hd⟩
      refine ⟨⟨?_, h⟩, hd⟩
      rintro rfl; rw [I_dep_zero] at hd; omega
  rw [hset, ← sum_filter_add_sum_filter_not (range (2 ^ q)) (fun ξ => dep q ξ ≤ j0) f]
  ring

/-- Bound form of `r^{deep}(v) = r_E(v) − r^{sh}(v)`: `‖r^{deep}(v)‖ ≤ r_E(v) + r^{sh}(v)`. -/
lemma I_rDeep_le (q s L j0 : ℕ) (hj0 : j0 ≤ q) (v : ℕ) :
    ‖rDeep q s L j0 v‖ ≤
      ∑ z ∈ Eset q (hL s L), ∑ z' ∈ Eset q (hL s L),
          (if (2 : ℤ) ^ q ∣ (z' : ℤ) - z + (v : ℤ) then (1 : ℝ) else 0) +
        (2 : ℝ) ^ j0 / 2 ^ q * ∑ z ∈ Eset q (hL s L), ∑ z' ∈ Eset q (hL s L),
          (if (2 : ℤ) ^ j0 ∣ (z' : ℤ) - z + (v : ℤ) then (1 : ℝ) else 0) := by
  set E := Eset q (hL s L) with hE
  unfold rDeep
  rw [← hE, I_deep_split]
  have hall := I_corr_expand q E (range (2 ^ q)) v
  have hsh := I_corr_expand q E ((range (2 ^ q)).filter (fun ξ => dep q ξ ≤ j0)) v
  simp only [Int.cast_natCast] at hall hsh
  rw [hall, hsh]
  simp_rw [I_sum_eC_pow, I_sum_shallow q j0 hj0]
  -- rewrite as a sum of real numbers
  have e1 : ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ q ∣ (z' : ℤ) - z + v then (2 : ℂ) ^ q else 0) =
      (2 : ℂ) ^ q * ((∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ q ∣ (z' : ℤ) - z + (v : ℤ) then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    push_cast; rw [mul_sum]; apply sum_congr rfl; intro z _; rw [mul_sum]; apply sum_congr rfl
    intro z' _; split_ifs <;> simp
  have e2 : ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ j0 ∣ (z' : ℤ) - z + v then (2 : ℂ) ^ j0 else 0) =
      (2 : ℂ) ^ j0 * ((∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ j0 ∣ (z' : ℤ) - z + (v : ℤ) then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    push_cast; rw [mul_sum]; apply sum_congr rfl; intro z _; rw [mul_sum]; apply sum_congr rfl
    intro z' _; split_ifs <;> simp
  rw [e1, e2]
  set a : ℝ := ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ q ∣ (z' : ℤ) - z + (v : ℤ) then (1 : ℝ) else 0)
  set b : ℝ := ∑ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ j0 ∣ (z' : ℤ) - z + (v : ℤ) then (1 : ℝ) else 0)
  have ha : 0 ≤ a := sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hb : 0 ≤ b := sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hc : (2 : ℂ)⁻¹ ^ q * ((2 : ℂ) ^ q * (a : ℂ) - (2 : ℂ) ^ j0 * (b : ℂ)) =
      ((a - (2 : ℝ) ^ j0 / 2 ^ q * b : ℝ) : ℂ) := by
    push_cast; rw [inv_pow]; field_simp
  rw [hc, Complex.norm_real, Real.norm_eq_abs]
  have hq0 : 0 ≤ (2 : ℝ) ^ j0 / 2 ^ q * b := by positivity
  rw [abs_le]; constructor <;> linarith

/-- Parseval: if `E ⊆ [0, 2^q)`, then `W = 2^q|E| − |E|²`. -/
lemma I_parseval (q : ℕ) (E : Finset ℕ) (hE : E ⊆ range (2 ^ q)) :
    Wsum q E = 2 ^ q * E.card - (E.card : ℝ) ^ 2 := by
  have hall := I_corr_expand q E (range (2 ^ q)) 0
  simp_rw [I_sum_eC_pow] at hall
  have hdiag : ∀ z ∈ E, ∑ z' ∈ E, (if (2 : ℤ) ^ q ∣ ((z' : ℤ) - z + (0 : ℤ)) then (2 : ℂ) ^ q else 0) =
      (2 : ℂ) ^ q := by
    intro z hz
    rw [sum_eq_single z]
    · simp
    · intro z' hz' hne
      rw [if_neg]
      intro hd
      apply hne
      have hz1 := mem_range.mp (hE hz)
      have hz2 := mem_range.mp (hE hz')
      have hmod : z ≡ z' [MOD 2 ^ q] := by
        rw [Nat.modEq_iff_dvd]; push_cast; simpa using hd
      rw [Nat.ModEq, Nat.mod_eq_of_lt hz1, Nat.mod_eq_of_lt hz2] at hmod
      exact hmod.symm
    · intro h; exact absurd hz h
  rw [sum_congr rfl hdiag, sum_const, nsmul_eq_mul] at hall
  simp only [Int.cast_zero, zero_mul, zero_div, I_eC_zero, mul_one] at hall
  have hreal : ∑ ξ ∈ range (2 ^ q), ‖Ehat q E ξ‖ ^ 2 = 2 ^ q * E.card := by
    have : ((∑ ξ ∈ range (2 ^ q), ‖Ehat q E ξ‖ ^ 2 : ℝ) : ℂ) = ((2 ^ q * E.card : ℝ) : ℂ) := by
      push_cast; rw [hall]; ring
    exact_mod_cast this
  have h0 : ‖Ehat q E ((0 : ℕ) : ℤ)‖ = E.card := by
    unfold Ehat; simp [I_eC_zero]
  unfold Wsum
  rw [← hreal, ← add_sum_erase (range (2 ^ q)) (fun ξ => ‖Ehat q E ξ‖ ^ 2) (mem_range.mpr (by positivity)),
    h0]
  ring

/-! ## Upper bound on the average against `μ` -/

/-- The second half of Lemma 11.2: if `|E| ≤ 2^{q−1}`, `|E| > 0` and `ϖ_{j₀} ≤ 1/2`, then
`‖Σ_ξ μ(ξ) e(vξ/2^q)‖ ≤ (2/(1−ϖ_{j₀})) ϱ_E(v)`. -/
lemma I_mu_sum_le (q s L j0 : ℕ) (hq : 1 ≤ q) (hE : ((Eset q (hL s L)).card : ℝ) ≤ 2 ^ (q - 1))
    (hEpos : 0 < (Eset q (hL s L)).card) (hvar : varpi q s L j0 ≤ 1 / 2) (v : ℕ) :
    ‖∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) * eC ((v : ℝ) * ξ / 2 ^ q)‖ ≤
      2 / (1 - varpi q s L j0) * rhoE q s L j0 v := by
  set E := Eset q (hL s L) with hEdef
  have hEsub : E ⊆ range (2 ^ q) := by
    intro z hz; rw [hEdef] at hz; simp only [Eset, Finset.mem_filter] at hz; exact hz.1
  have hW := I_parseval q E hEsub
  set W := Wsum q E with hWdef
  set e : ℝ := (E.card : ℝ) with he
  have he0 : 0 < e := by rw [he]; exact_mod_cast hEpos
  have hq2 : (2 : ℝ) ^ q = 2 * 2 ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hWlow : 2 ^ q * e ≤ 2 * W := by
    rw [hW]; nlinarith
  have hWpos : 0 < W := by
    have : (0 : ℝ) < 2 ^ q * e := by positivity
    linarith
  have h1v : 0 < 1 - varpi q s L j0 := by linarith
  set Z := (1 - varpi q s L j0) * W with hZ
  have hZpos : 0 < Z := mul_pos h1v hWpos
  -- write the sum over `μ` in terms of `r^{deep}`
  have hsum : ∑ ξ ∈ range (2 ^ q), (muDeep q s L j0 ξ : ℂ) * eC ((v : ℝ) * ξ / 2 ^ q) =
      ((2 ^ q / Z : ℝ) : ℂ) * rDeep q s L j0 v := by
    unfold rDeep muDeep
    rw [← hEdef, ← hZ]
    rw [sum_filter, sum_erase]
    · rw [mul_sum, mul_sum]
      apply sum_congr rfl; intro ξ _
      by_cases h : ξ ≠ 0 ∧ j0 < dep q ξ
      · rw [if_pos h, if_pos h.2]; push_cast; rw [inv_pow]; field_simp
      · rw [if_neg h]
        by_cases h2 : j0 < dep q ξ
        · have : ξ = 0 := by by_contra h0; exact h ⟨h0, h2⟩
          subst this; rw [I_dep_zero] at h2; omega
        · rw [if_neg h2]; simp
    · simp [I_dep_zero]
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold rhoE
  rw [← hEdef, ← he]
  set r := ‖rDeep q s L j0 v‖ with hr
  have hkey : 2 ^ q * e / Z ≤ 2 / (1 - varpi q s L j0) := by
    rw [div_le_div_iff₀ hZpos h1v, hZ]; nlinarith
  calc 2 ^ q / Z * r = (2 ^ q * e / Z) * (r / e) := by field_simp
    _ ≤ 2 / (1 - varpi q s L j0) * (r / e) :=
      mul_le_mul_of_nonneg_right hkey (div_nonneg (norm_nonneg _) he0.le)

end Collatz.M1
