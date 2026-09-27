import Mathlib

/-!
# The part of `CollatzProof.Defs` used by the main theorem of the author's companion paper *A power-saving bound, uniform in the endpoint, for Collatz orbits that stay above a fixed barrier*

The shortcut map `T` and two lemmas about it, moved here from `CollatzProof.Defs` without changing their statements
or proofs (2026-09-26: separation of the minimal closure of that main theorem in the source repository).
`CollatzProof.Defs` imports this file.
-/

namespace Collatz

/-- The shortcut map `T(n) = n/2` (even), `(3n+1)/2` (odd). -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

lemma two_mul_T_of_odd {m : ℕ} (h : m % 2 = 1) : 2 * T m = 3 * m + 1 := by
  unfold T; split_ifs <;> omega

lemma two_mul_T_of_even {m : ℕ} (h : m % 2 = 0) : 2 * T m = m := by
  unfold T; split_ifs <;> omega

end Collatz
