import Mathlib
import CollatzProof.Core.Defs

/-!
# Basic definitions: the shortcut map `T`, the number of odd steps `o`, the additive term `c`, the dual Terras identity

Corresponds to Lemma 3.2 (i) of the paper (the dual Terras identity; Lemma 1.2 (i) of the proof manuscript).

(2026-09-26: the declarations in the dependency closure of the main theorem of the author's companion paper *A power-saving bound, uniform in the endpoint, for Collatz orbits that stay above a fixed barrier* were moved to `CollatzProof.Core.Defs`; this file contains the remaining declarations.)
-/

namespace Collatz

/-- The number of odd steps among the first `j` steps, `o_j(n)`. -/
def o (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => o n j + (if T^[j] n % 2 = 1 then 1 else 0)

/-- The additive term `c_j(n)`: `c_0 = 0`, and at an odd step `c_{j+1} = 3 c_j + 2^j`. -/
def c (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if T^[j] n % 2 = 1 then 3 * c n j + 2 ^ j else c n j

/-- The dual Terras identity `2^j T^j(n) = 3^{o_j} n + c_j`. -/
theorem dual (n j : ℕ) : 2 ^ j * T^[j] n = 3 ^ (o n j) * n + c n j := by
  induction j with
  | zero => simp [o, c]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : T^[j] n % 2 = 1
    · have h2 := two_mul_T_of_odd h
      simp only [o, c, h, ↓reduceIte, pow_succ]
      calc 2 ^ j * 2 * T (T^[j] n) = 2 ^ j * (2 * T (T^[j] n)) := by ring
        _ = 2 ^ j * (3 * T^[j] n + 1) := by rw [h2]
        _ = 3 * (2 ^ j * T^[j] n) + 2 ^ j := by ring
        _ = 3 ^ o n j * 3 * n + (3 * c n j + 2 ^ j) := by rw [ih]; ring
    · have h' : T^[j] n % 2 = 0 := by omega
      have h2 := two_mul_T_of_even h'
      simp only [o, c, h, ↓reduceIte, add_zero, pow_succ]
      calc 2 ^ j * 2 * T (T^[j] n) = 2 ^ j * (2 * T (T^[j] n)) := by ring
        _ = 2 ^ j * T^[j] n := by rw [h2]
        _ = 3 ^ o n j * n + c n j := ih

end Collatz
