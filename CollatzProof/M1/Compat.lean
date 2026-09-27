import Mathlib

/-!
# Formalization of the main theorem: lemmas absorbing differences between Lean/Mathlib versions

So that the same sources build both in `lean/` (Lean v4.34.1, Mathlib v4.34.1) and in `lean-nd/` (Lean v4.30.0-rc2, Mathlib v4.30.0-rc2),
this file provides replacements for lemmas whose names or arguments change between versions. Each is proved using only lemmas present in both versions.
- `Finset.prod_le_one₀` (v4.34) and `Finset.prod_le_one` (v4.30) → `cpt_prod_le_one`.
- `Nat.lt_mul_div_self_add` (only in Lean core of v4.34) → `cpt_lt_mul_div_self_add`.
- `padicValRat.zpow` (only in v4.34), `padicValRat.pow` (takes `q ≠ 0` in v4.30, not in v4.34)
  → `cpt_padicValRat_zpow`, `cpt_padicValRat_pow`.
-/

namespace Collatz.M1

/-- A finite product of values in `[0, 1]` is at most 1 (replacement for `Finset.prod_le_one₀`, real-valued). -/
theorem cpt_prod_le_one {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hA := h0 a (Finset.mem_insert_self a s)
    have hB := h1 a (Finset.mem_insert_self a s)
    have hP : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have hQ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    nlinarith

/-- `x < k·⌊x/k⌋ + k` (replacement for `Nat.lt_mul_div_self_add`). -/
theorem cpt_lt_mul_div_self_add {x k : ℕ} (h : 0 < k) : x < k * (x / k) + k := by
  have h1 := Nat.mod_add_div x k
  have h2 := Nat.mod_lt x h
  linarith

/-- `v_p(q^n) = n·v_p(q)` (`q ≠ 0`; replacement for `padicValRat.pow`). -/
theorem cpt_padicValRat_pow {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) (n : ℕ) :
    padicValRat p (q ^ n) = n * padicValRat p q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicValRat.mul (pow_ne_zero _ hq) hq, ih]
    push_cast; ring

/-- `v_p(q^k) = k·v_p(q)` (`q ≠ 0`, `k ∈ ℤ`; replacement for `padicValRat.zpow`). -/
theorem cpt_padicValRat_zpow {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) (k : ℤ) :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, cpt_padicValRat_pow hq]
  · rw [zpow_neg, zpow_natCast, padicValRat.inv, cpt_padicValRat_pow hq]
    ring

end Collatz.M1
