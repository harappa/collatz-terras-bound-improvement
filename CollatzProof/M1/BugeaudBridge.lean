import CollatzProof.M1.DeepDefs
import CollatzProof.M1.Compat

/-!
# Theorem 2 of Bugeaud (2002) for general `m` and the hypothesis `BugeaudHyp` (Proposition B.1 of the paper; suggested in a review of the manuscript)

Y. Bugeaud, *Linear forms in two m-adic logarithms and applications to Diophantine problems*,
Compositio Math. **132** (2002), 137–158, §2 (pp. 138–140, checked against the typeset pages of the original paper). We state
its Theorem 2 **for general `m` and `μ`, as in the original**, as the proposition `Thm2 m μ`, and check in the kernel that the
frozen hypothesis `BugeaudHyp` (`DeepDefs.lean`: `m = 8`, `μ = 4`, multiplicatively independent case, `c₂(4) = 53.6`) follows
from `Thm2 8 4` (`bugeaudHyp_of_thm2`). All specializations (`m = 8 = 2^3`, `μ = 4`, `x_i/y_i` written in lowest terms) are
made inside the proof of the bridge.

**Correspondence with the original** (pp. 138–140):
- `m > 1` is an integer, `m = p₁^{u₁}⋯p_w^{u_w}`. The `p_i` are the elements of `m.primeFactors`, `u_i` is `m.factorization p_i`.
- For an integer `x ≠ 0`, `v_m(x)` is the largest `v ≥ 0` with `m^v ∣ x` (`vmNat`). The observation of the original
  `v_m(x) = min_i ⌊v_{p_i}(x)/u_i⌋` is the lemma `vmNat_eq_inf'`. For `a/b` in lowest terms, `v_m(a/b) = v_m(a) − v_m(b)` (`vm`).
- `x₁/y₁`, `x₂/y₂` are nonzero rational numbers with `x₁/y₁ ≠ ±1`, `b₁, b₂` are positive integers, `Λ = (x₁/y₁)^{b₁} − (x₂/y₂)^{b₂}`,
  and `v_{p_i}(x₁/y₁) = v_{p_i}(x₂/y₂) = 0` for all `i`.
- (H1): `g` is a positive integer coprime to `p₁⋯p_w` with `v_{p_i}((x₁/y₁)^g − 1) ≥ u_i` and `v_{p_i}((x₂/y₂)^g − 1) ≥ 1` for all `i`.
- (H2): if `2 ∣ m`, then `v₂((x₁/y₁)^g − 1) ≥ 2` and `v₂((x₂/y₂)^g − 1) ≥ 2`.
- `A₁, A₂ > 1` satisfy `log A_i ≥ max{log|x_i|, log|y_i|, log m}`, and `b' = b₁/log A₂ + b₂/log A₁`.
- Theorem 2: `μ ∈ {4, 6, 8, 10, 15}` with the table of `c₁(μ)`, `c₂(μ)`. Under (H1) and (H2), if `m`, `b₁`, `b₂` are relatively prime,
  `v_m(Λ) ≤ c₁(μ) g/(log m)^4 · (max{log b' + log log m + 0.64, μ log m})² log A₁ log A₂`.
  If `x₁/y₁` and `x₂/y₂` are multiplicatively independent, `c₁(μ)` may be replaced by `c₂(μ)`.

**Choices made in the Lean statement** (none of them strengthens the original statement; each is weaker or equivalent):
1. `x_i, y_i` are nonzero integers (the original does not require lowest terms). The condition on `log A_i` is weakest for the
   representation in lowest terms, so this is equivalent to the form restricted to lowest terms.
2. `v_p(z) ≥ k` is `z = 0 ∨ k ≤ padicValRat p z` (`VpGe`, with the convention `v_p(0) = +∞`). Using Mathlib's `padicValRat p 0 = 0`
   directly would drop the case `(x₂/y₂)^g = 1`.
3. `Λ ≠ 0` is a premise. The original defines `v_m` only for nonzero rational numbers, so it assumes this implicitly (in the `c₁` form
   `Λ = 0` does occur: `lam_zero_case`). The value `vm m 0 = 0` (`vmNat m 0 = 0`) is never used. In the independent case `Λ ≠ 0`
   follows (`lam_ne_zero_of_indep`).
4. "`m`, `b₁`, `b₂` are relatively prime" means that the gcd of the three numbers is 1 (`Nat.gcd m (Nat.gcd b₁ b₂) = 1`), i.e. no prime
   factor of `m` divides both `b₁` and `b₂`. This is the reading of the remark on p. 140 ("the term `h` of Theorem 1 is then positive"; "satisfied since `b₁` or `b₂` is 1"; the latter excludes the reading "pairwise coprime").
5. Theorem 1 of the original additionally assumes "`p_i ∤ b₂/p_i^{h_i}`". In case the proof of Theorem 2 needs it, we also state the
   weaker form `Thm2C2Narrow` with the extra premise `∀ p ∈ m.primeFactors, ¬ p ∣ b₂`, and show that `BugeaudHyp` follows from it too
   (`bugeaudHyp_of_thm2C2Narrow`). `BugeaudHyp` assumes "`b₂` is odd", which satisfies both readings.
6. `g` is any positive integer satisfying (H1) and (H2) (the original says "if there exists such a `g`" and does not require minimality).
7. Outside the table, `c₁` and `c₂` are set to 0; this is never used, since `Hyps` requires `μ ∈ {4, 6, 8, 10, 15}`.

**Degeneracy check**: the premises of `Thm2C2 8 4` can be satisfied (`hyps_example`: `x₁/y₁ = 9`, `x₂/y₂ = 5`, `g = b₁ = b₂ = 1`,
`A₁ = 9`, `A₂ = 8` satisfy `Hyps`, independence and `Λ = 4 ≠ 0`). An example with `Λ = 0` in the `c₁` form is `lam_zero_case`.
The bridge uses only the `Thm2C2` part (indeed only the weaker `Thm2C2Narrow`), not `Thm2C1`.
-/

namespace Collatz.M1

namespace Bugeaud

open Real

/-! ## The `m`-adic valuation -/

/-- The `m`-adic valuation of a natural number `n`: the largest `v` with `m^v ∣ n` (the definition on p. 138 of the original).
The bound `n` of `Nat.findGreatest` is harmless: for `n ≠ 0` and `m ≥ 2`, `m^v ∣ n ⇒ v < 2^v ≤ m^v ≤ n` (`vmNat_eq_of_iff`).
For `n = 0` the value is 0 (the original defines `v_m` only for nonzero numbers; `Thm2C1` and `Thm2C2` below assume `Λ ≠ 0`, so this value is never used). -/
def vmNat (m n : ℕ) : ℕ := Nat.findGreatest (fun v => m ^ v ∣ n) n

/-- The `m`-adic valuation of a rational number (p. 138 of the original): `v_m(a) − v_m(b)` for `a/b` in lowest terms. `x.num` and `x.den` are coprime and `x.den > 0`.
For an integer `a`, `v_m(a)` is taken of `|a|` (`m^v ∣ a ↔ m^v ∣ |a|`). -/
def vm (m : ℕ) (x : ℚ) : ℤ := (vmNat m x.num.natAbs : ℤ) - (vmNat m x.den : ℤ)

/-- `v < 2^v` (replacement for `Nat.lt_two_pow_self`, whose signature differs between versions). -/
lemma lt_two_pow' (v : ℕ) : v < 2 ^ v := by
  induction v with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- If `m^v ∣ n` is equivalent to `v ≤ K`, then `vmNat m n = K` (`m ≥ 2`, `n ≠ 0`). -/
lemma vmNat_eq_of_iff {m n K : ℕ} (hm : 1 < m) (hn : n ≠ 0) (h : ∀ v, m ^ v ∣ n ↔ v ≤ K) :
    vmNat m n = K := by
  unfold vmNat
  rw [Nat.findGreatest_eq_iff]
  have hK : m ^ K ∣ n := (h K).mpr le_rfl
  refine ⟨?_, fun _ => hK, fun j hj _ hdvd => absurd ((h j).mp hdvd) (by omega)⟩
  have h1 : m ^ K ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hK
  have h2 : 2 ^ K ≤ m ^ K := Nat.pow_le_pow_left hm K
  have h3 := lt_two_pow' K
  omega

/-- `m^v ∣ n ↔ u_p v ≤ v_p(n)` for every prime `p ∣ m` (`m, n ≠ 0`). -/
lemma pow_dvd_iff_forall {m n v : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    m ^ v ∣ n ↔ ∀ p ∈ m.primeFactors, v * m.factorization p ≤ padicValNat p n := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero v hm) hn, Nat.factorization_pow, Finsupp.le_def]
  constructor
  · intro h p hp
    have h' := h p
    simp only [Finsupp.smul_apply, smul_eq_mul] at h'
    rwa [← Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
  · intro h p
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hp : p ∈ m.primeFactors
    · rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
      exact h p hp
    · have h0 : m.factorization p = 0 := by
        by_contra hne
        exact hp (by rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hne)
      rw [h0, mul_zero]
      exact Nat.zero_le _

/-- The observation on p. 138 of the original: `v_m(x) = min_{1 ≤ i ≤ w} ⌊v_{p_i}(x)/u_i⌋` (`m > 1`, `n ≠ 0`). -/
lemma vmNat_eq_inf' {m n : ℕ} (hm : 1 < m) (hn : n ≠ 0) :
    vmNat m n = m.primeFactors.inf' (Nat.nonempty_primeFactors.mpr hm)
      (fun p => padicValNat p n / m.factorization p) := by
  apply vmNat_eq_of_iff hm hn
  intro v
  rw [pow_dvd_iff_forall (by omega) hn, Finset.le_inf'_iff]
  refine forall₂_congr (fun p hp => ?_)
  have hu : 0 < m.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact hp))
  exact (Nat.le_div_iff_mul_le hu).symm

/-! ## Theorem 2 of the original -/

/-- The set `{4, 6, 8, 10, 15}` of values of `μ` in the original. -/
def muSet : Finset ℕ := {4, 6, 8, 10, 15}

/-- `c₁(μ)` from the table of the original (p. 140). 0 for `μ` outside the table (never used, since `Hyps` requires `μ ∈ muSet`). -/
noncomputable def c1 (μ : ℕ) : ℝ :=
  if μ = 4 then 66.8 else if μ = 6 then 46.1 else if μ = 8 then 36.9 else
    if μ = 10 then 32 else if μ = 15 then 26.1 else 0

/-- `c₂(μ)` from the table of the original (p. 140, multiplicatively independent case). 0 for `μ` outside the table. -/
noncomputable def c2 (μ : ℕ) : ℝ :=
  if μ = 4 then 53.6 else if μ = 6 then 35.5 else if μ = 8 then 27.4 else
    if μ = 10 then 22.9 else if μ = 15 then 18 else 0

/-- `v_p(z) ≥ k` (with the convention `v_p(0) = +∞`). -/
def VpGe (p : ℕ) (z : ℚ) (k : ℤ) : Prop := z = 0 ∨ k ≤ padicValRat p z

/-- The setting of §2 of the original and the hypotheses of Theorem 2 (pp. 138–140). `x_i/y_i` is `(x_i : ℚ) / y_i`. -/
def Hyps (m μ : ℕ) (x₁ y₁ x₂ y₂ : ℤ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ) : Prop :=
  -- `m > 1` is an integer (p. 138), `μ ∈ {4, 6, 8, 10, 15}` (Theorem 2)
  1 < m ∧ μ ∈ muSet ∧
  -- `x₁/y₁`, `x₂/y₂` are nonzero rational numbers with `x₁/y₁ ≠ ±1`; `b₁`, `b₂` are positive integers (p. 138)
  x₁ ≠ 0 ∧ y₁ ≠ 0 ∧ x₂ ≠ 0 ∧ y₂ ≠ 0 ∧ (x₁ / y₁ : ℚ) ≠ 1 ∧ (x₁ / y₁ : ℚ) ≠ -1 ∧ 0 < b₁ ∧ 0 < b₂ ∧
  -- `v_{p_i}(x₁/y₁) = v_{p_i}(x₂/y₂) = 0` for all `i` (pp. 138–139)
  (∀ p ∈ m.primeFactors, padicValRat p (x₁ / y₁ : ℚ) = 0 ∧ padicValRat p (x₂ / y₂ : ℚ) = 0) ∧
  -- (H1): `g` is a positive integer coprime to `p₁⋯p_w` and, for all `i`,
  -- `v_{p_i}((x₁/y₁)^g − 1) ≥ u_i` and `v_{p_i}((x₂/y₂)^g − 1) ≥ 1` (p. 139)
  0 < g ∧ Nat.Coprime g (∏ p ∈ m.primeFactors, p) ∧
  (∀ p ∈ m.primeFactors, VpGe p ((x₁ / y₁ : ℚ) ^ g - 1) (m.factorization p) ∧
    VpGe p ((x₂ / y₂ : ℚ) ^ g - 1) 1) ∧
  -- (H2): if `2 ∣ m`, then `v₂((x₁/y₁)^g − 1) ≥ 2` and `v₂((x₂/y₂)^g − 1) ≥ 2` (p. 139)
  (2 ∣ m → VpGe 2 ((x₁ / y₁ : ℚ) ^ g - 1) 2 ∧ VpGe 2 ((x₂ / y₂ : ℚ) ^ g - 1) 2) ∧
  -- `A₁, A₂ > 1` and `log A_i ≥ max{log|x_i|, log|y_i|, log m}` (p. 140)
  1 < A₁ ∧ 1 < A₂ ∧
  max (Real.log |(x₁ : ℝ)|) (max (Real.log |(y₁ : ℝ)|) (Real.log m)) ≤ Real.log A₁ ∧
  max (Real.log |(x₂ : ℝ)|) (max (Real.log |(y₂ : ℝ)|) (Real.log m)) ≤ Real.log A₂ ∧
  -- `m`, `b₁`, `b₂` are relatively prime (Theorem 2: no prime factor of `m` divides both `b₁` and `b₂`)
  Nat.gcd m (Nat.gcd b₁ b₂) = 1

/-- The right-hand side of the original, `c g/(log m)^4 · (max{log b' + log log m + 0.64, μ log m})² log A₁ log A₂`,
with `b' = b₁/log A₂ + b₂/log A₁` (p. 140). -/
noncomputable def rhs (m μ : ℕ) (c : ℝ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ) : ℝ :=
  c * g / (Real.log m) ^ 4 *
    (max (Real.log (b₁ / Real.log A₂ + b₂ / Real.log A₁) + Real.log (Real.log m) + 0.64)
      (μ * Real.log m)) ^ 2 * Real.log A₁ * Real.log A₂

/-- The first part of Theorem 2 of the original (`c₁(μ)`, multiplicative independence not assumed). -/
def Thm2C1 (m μ : ℕ) : Prop :=
  ∀ (x₁ y₁ x₂ y₂ : ℤ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ),
    Hyps m μ x₁ y₁ x₂ y₂ g b₁ b₂ A₁ A₂ →
    (x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂ ≠ 0 →
    (vm m ((x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂) : ℝ) ≤ rhs m μ (c1 μ) g b₁ b₂ A₁ A₂

/-- The second part of Theorem 2 of the original (`c₂(μ)` if `x₁/y₁` and `x₂/y₂` are multiplicatively independent). -/
def Thm2C2 (m μ : ℕ) : Prop :=
  ∀ (x₁ y₁ x₂ y₂ : ℤ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ),
    Hyps m μ x₁ y₁ x₂ y₂ g b₁ b₂ A₁ A₂ →
    MulIndep (x₁ / y₁ : ℚ) (x₂ / y₂ : ℚ) →
    (x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂ ≠ 0 →
    (vm m ((x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂) : ℝ) ≤ rhs m μ (c2 μ) g b₁ b₂ A₁ A₂

/-- **Theorem 2 of the original** (for fixed `m`, `μ`; `Hyps` requires `1 < m` and `μ ∈ {4, 6, 8, 10, 15}`). -/
def Thm2 (m μ : ℕ) : Prop := Thm2C1 m μ ∧ Thm2C2 m μ

/-- Theorem 2 of the original in full (all `m`, `μ`). -/
def Thm2All : Prop := ∀ m μ : ℕ, Thm2 m μ

/-- `Thm2C2` with the condition "`p_i ∤ b₂/p_i^{h_i}`" of Theorem 1 of the original added as a premise, in the case `h_i = 0` (with more premises, this is a weaker statement than `Thm2C2`). -/
def Thm2C2Narrow (m μ : ℕ) : Prop :=
  ∀ (x₁ y₁ x₂ y₂ : ℤ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ),
    Hyps m μ x₁ y₁ x₂ y₂ g b₁ b₂ A₁ A₂ →
    (∀ p ∈ m.primeFactors, ¬ p ∣ b₂) →
    MulIndep (x₁ / y₁ : ℚ) (x₂ / y₂ : ℚ) →
    (x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂ ≠ 0 →
    (vm m ((x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂) : ℝ) ≤ rhs m μ (c2 μ) g b₁ b₂ A₁ A₂

/-- From the original form to the weaker form (the added premise is simply discarded). -/
theorem thm2C2Narrow_of_thm2C2 {m μ : ℕ} (h : Thm2C2 m μ) : Thm2C2Narrow m μ :=
  fun x₁ y₁ x₂ y₂ g b₁ b₂ A₁ A₂ hH _ hI hΛ => h x₁ y₁ x₂ y₂ g b₁ b₂ A₁ A₂ hH hI hΛ

/-! ## Specialization to `m = 8` -/

lemma eight_eq : (8 : ℕ) = 2 ^ 3 := by norm_num

lemma primeFactors_eight : Nat.primeFactors 8 = {2} := by
  rw [eight_eq]; exact Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two

lemma factorization_eight_two : Nat.factorization 8 2 = 3 := by
  rw [eight_eq]; exact Nat.factorization_pow_self Nat.prime_two

/-- `v_8(n) = ⌊v_2(n)/3⌋` (for `n = 0` both sides are 0). -/
lemma vmNat_eight (n : ℕ) : vmNat 8 n = padicValNat 2 n / 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vmNat]
  apply vmNat_eq_of_iff (by norm_num) hn.ne'
  intro v
  rw [pow_dvd_iff_forall (by norm_num) hn.ne', primeFactors_eight]
  simp only [Finset.mem_singleton, forall_eq, factorization_eight_two]
  exact (Nat.le_div_iff_mul_le (by norm_num)).symm

/-- `vm 8` agrees with `v8` of `DeepDefs.lean` (for all rational numbers). -/
lemma vm_eight (x : ℚ) : vm 8 x = v8 x := by
  unfold vm v8
  rw [vmNat_eight, vmNat_eight]
  rfl

/-- `v2q` is `padicValRat 2`. -/
lemma v2q_eq (x : ℚ) : v2q x = padicValRat 2 x := rfl

/-- For `m = 8`, `μ = 4`, `c₂(4) = 53.6` the right-hand side is that of `BugeaudHyp`. -/
lemma rhs_eight_four (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ) :
    rhs 8 4 (c2 4) g b₁ b₂ A₁ A₂ =
      53.6 * g / (Real.log 8) ^ 4 *
        (max (Real.log (b₁ / Real.log A₂ + b₂ / Real.log A₁) + Real.log (Real.log 8) + 0.64)
          (4 * Real.log 8)) ^ 2 * Real.log A₁ * Real.log A₂ := by
  have hc : c2 4 = 53.6 := by simp [c2]
  simp only [rhs, hc, Nat.cast_ofNat]

/-- Representation in lowest terms: `(r.num : ℚ) / ((r.den : ℤ) : ℚ) = r`. -/
lemma num_div_den' (r : ℚ) : ((r.num : ℚ) / (((r.den : ℤ)) : ℚ)) = r := by
  rw [Int.cast_natCast]; exact Rat.num_div_den r

/-- Multiplicative independence implies `Λ ≠ 0` (`b₁ ≥ 1`). -/
lemma lam_ne_zero_of_indep {r₁ r₂ : ℚ} {b₁ b₂ : ℕ} (hr₂ : r₂ ≠ 0) (hb₁ : 1 ≤ b₁)
    (hI : MulIndep r₁ r₂) : r₁ ^ b₁ - r₂ ^ b₂ ≠ 0 := by
  intro h
  have heq : r₁ ^ b₁ = r₂ ^ b₂ := sub_eq_zero.mp h
  have h1 : r₁ ^ (b₁ : ℤ) * r₂ ^ (-(b₂ : ℤ)) = 1 := by
    rw [zpow_neg, zpow_natCast, zpow_natCast, heq]
    exact mul_inv_cancel₀ (pow_ne_zero _ hr₂)
  have := (hI _ _ h1).1
  omega

/-- If `b₂` is odd, then `8`, `b₁`, `b₂` are relatively prime. -/
lemma gcd_eight_of_odd {b₁ b₂ : ℕ} (hb : b₂ % 2 = 1) : Nat.gcd 8 (Nat.gcd b₁ b₂) = 1 := by
  have h2 : Nat.Coprime 2 b₂ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have h8 : Nat.Coprime 8 b₂ := by rw [eight_eq]; exact Nat.Coprime.pow_left 3 h2
  exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right b₁ b₂) h8

/-- The premises of `BugeaudHyp` imply the premises `Hyps 8 4` of the original for the representation in lowest terms `x_i = r_i.num`, `y_i = r_i.den`. -/
lemma hyps_of_bugeaud (r₁ r₂ : ℚ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (h1 : r₁ ≠ 1) (hm1 : r₁ ≠ -1) (hv₁ : v2q r₁ = 0) (hv₂ : v2q r₂ = 0)
    (hg : 1 ≤ g) (hgo : g % 2 = 1) (hH₁ : 3 ≤ v2q (r₁ ^ g - 1)) (hH₂ : 2 ≤ v2q (r₂ ^ g - 1))
    (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂) (hb₂o : b₂ % 2 = 1)
    (hA₁ : 1 < A₁) (hA₂ : 1 < A₂)
    (hx₁ : Real.log |(r₁.num : ℝ)| ≤ Real.log A₁) (hy₁ : Real.log (r₁.den : ℝ) ≤ Real.log A₁)
    (h8₁ : Real.log 8 ≤ Real.log A₁)
    (hx₂ : Real.log |(r₂.num : ℝ)| ≤ Real.log A₂) (hy₂ : Real.log (r₂.den : ℝ) ≤ Real.log A₂)
    (h8₂ : Real.log 8 ≤ Real.log A₂) :
    Hyps 8 4 r₁.num r₁.den r₂.num r₂.den g b₁ b₂ A₁ A₂ := by
  rw [v2q_eq] at hv₁ hv₂ hH₁ hH₂
  have hden : ∀ r : ℚ, Real.log |(((r.den : ℤ)) : ℝ)| = Real.log (r.den : ℝ) := by
    intro r; rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
  have hlog8 : Real.log ((8 : ℕ) : ℝ) = Real.log 8 := by rw [Nat.cast_ofNat]
  simp only [Hyps, num_div_den', primeFactors_eight, Finset.mem_singleton, forall_eq,
    Finset.prod_singleton, factorization_eight_two, hden, hlog8]
  refine ⟨by norm_num, by decide, Rat.num_ne_zero.mpr hr₁, by exact_mod_cast r₁.den_nz,
    Rat.num_ne_zero.mpr hr₂, by exact_mod_cast r₂.den_nz, h1, hm1, by omega, by omega, ⟨hv₁, hv₂⟩,
    by omega, ?_, ⟨Or.inr (by exact_mod_cast hH₁), Or.inr (by linarith)⟩,
    fun _ => ⟨Or.inr (by linarith), Or.inr hH₂⟩, hA₁, hA₂,
    max_le hx₁ (max_le hy₁ h8₁), max_le hx₂ (max_le hy₂ h8₂), gcd_eight_of_odd hb₂o⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega) |>.symm

/-- **Bridge** (from the weaker form): `Thm2C2Narrow 8 4 → BugeaudHyp`. Take `x_i = r_i.num`, `y_i = r_i.den`, and rewrite with `vm 8 = v8` and the equality of the right-hand sides. -/
theorem bugeaudHyp_of_thm2C2Narrow (h : Thm2C2Narrow 8 4) : BugeaudHyp := by
  intro r₁ r₂ g b₁ b₂ A₁ A₂ hr₁ hr₂ h1 hm1 hv₁ hv₂ hg hgo hH₁ hH₂ hb₁ hb₂ hb₂o hI hA₁ hA₂
    hx₁ hy₁ h8₁ hx₂ hy₂ h8₂
  have hH := hyps_of_bugeaud r₁ r₂ g b₁ b₂ A₁ A₂ hr₁ hr₂ h1 hm1 hv₁ hv₂ hg hgo hH₁ hH₂ hb₁ hb₂ hb₂o
    hA₁ hA₂ hx₁ hy₁ h8₁ hx₂ hy₂ h8₂
  have hN : ∀ p ∈ Nat.primeFactors 8, ¬ p ∣ b₂ := by
    rw [primeFactors_eight]; intro p hp; rw [Finset.mem_singleton] at hp; subst hp; omega
  have key := h r₁.num r₁.den r₂.num r₂.den g b₁ b₂ A₁ A₂ hH hN
    (by rw [num_div_den', num_div_den']; exact hI)
    (by rw [num_div_den', num_div_den']; exact lam_ne_zero_of_indep hr₂ hb₁ hI)
  rw [num_div_den', num_div_den', vm_eight, rhs_eight_four] at key
  exact key

/-- **Bridge**: `BugeaudHyp` from the independent case of Theorem 2 of the original (`m = 8`, `μ = 4`). -/
theorem bugeaudHyp_of_thm2C2 (h : Thm2C2 8 4) : BugeaudHyp :=
  bugeaudHyp_of_thm2C2Narrow (thm2C2Narrow_of_thm2C2 h)

/-- **Bridge**: `BugeaudHyp` from Theorem 2 of the original (`m = 8`, `μ = 4`). -/
theorem bugeaudHyp_of_thm2 (h : Thm2 8 4) : BugeaudHyp :=
  bugeaudHyp_of_thm2C2 h.2

/-! ## Degeneracy checks -/

lemma pvr_zero_of_not_dvd (p n : ℕ) (q : ℚ) (hq : (n : ℚ) = q) (hd : ¬ p ∣ n) :
    padicValRat p q = 0 := by
  rw [← hq, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero]

lemma vpGe_of_dvd (p n k : ℕ) [Fact p.Prime] (q : ℚ) (hq : (n : ℚ) = q) (hn : n ≠ 0)
    (hd : p ^ k ∣ n) : VpGe p q k := by
  right
  rw [← hq, padicValRat.of_nat]
  exact_mod_cast (padicValNat_dvd_iff_le hn).mp hd

/-- `9` and `5` are multiplicatively independent (look at the 3-adic and 5-adic valuations). -/
lemma mulIndep_nine_five : MulIndep (9 : ℚ) 5 := by
  intro k₁ k₂ h
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h9 : (9 : ℚ) ≠ 0 := by norm_num
  have h5 : (5 : ℚ) ≠ 0 := by norm_num
  have hv : ∀ p : ℕ, [Fact p.Prime] →
      k₁ * padicValRat p 9 + k₂ * padicValRat p 5 = 0 := by
    intro p _
    have := congrArg (padicValRat p) h
    rwa [padicValRat.mul (zpow_ne_zero _ h9) (zpow_ne_zero _ h5), cpt_padicValRat_zpow h9,
      cpt_padicValRat_zpow h5, padicValRat.one] at this
  have a3 : padicValRat 3 (9 : ℚ) = 2 := by
    rw [show (9 : ℚ) = ((3 ^ 2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat.prime_pow]
    rfl
  have b3 : padicValRat 3 (5 : ℚ) = 0 := pvr_zero_of_not_dvd 3 5 5 (by norm_num) (by norm_num)
  have a5 : padicValRat 5 (9 : ℚ) = 0 := pvr_zero_of_not_dvd 5 9 9 (by norm_num) (by norm_num)
  have b5 : padicValRat 5 (5 : ℚ) = 1 := by
    rw [show (5 : ℚ) = ((5 ^ 1 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat.prime_pow]
    rfl
  have e3 := hv 3
  have e5 := hv 5
  rw [a3, b3] at e3
  rw [a5, b5] at e5
  constructor <;> linarith

/-- The premises of `Thm2C2 8 4` can be satisfied: `x₁/y₁ = 9`, `x₂/y₂ = 5`, `g = b₁ = b₂ = 1`, `A₁ = 9`, `A₂ = 8`
satisfy `Hyps`, multiplicative independence and `Λ = 4 ≠ 0`. -/
theorem hyps_example :
    Hyps 8 4 9 1 5 1 1 1 1 9 8 ∧ MulIndep ((9 : ℤ) / (1 : ℤ) : ℚ) ((5 : ℤ) / (1 : ℤ) : ℚ) ∧
      ((9 : ℤ) / (1 : ℤ) : ℚ) ^ 1 - ((5 : ℤ) / (1 : ℤ) : ℚ) ^ 1 ≠ 0 := by
  refine ⟨?_, ?_, by norm_num⟩
  · simp only [Hyps, primeFactors_eight, Finset.mem_singleton, forall_eq,
      Finset.prod_singleton, factorization_eight_two]
    norm_num
    refine ⟨by decide, ⟨pvr_zero_of_not_dvd 2 9 9 (by norm_num) (by norm_num),
      pvr_zero_of_not_dvd 2 5 5 (by norm_num) (by norm_num)⟩,
      ⟨vpGe_of_dvd 2 8 3 8 (by norm_num) (by norm_num) (by norm_num),
        vpGe_of_dvd 2 4 1 4 (by norm_num) (by norm_num) (by norm_num)⟩,
      ⟨vpGe_of_dvd 2 8 2 8 (by norm_num) (by norm_num) (by norm_num),
        vpGe_of_dvd 2 4 2 4 (by norm_num) (by norm_num) (by norm_num)⟩,
      ⟨Real.log_nonneg (by norm_num), Real.log_le_log (by norm_num) (by norm_num)⟩,
      Real.log_le_log (by norm_num) (by norm_num), Real.log_nonneg (by norm_num)⟩
  · have e9 : ((9 : ℤ) / (1 : ℤ) : ℚ) = 9 := by norm_num
    have e5 : ((5 : ℤ) / (1 : ℤ) : ℚ) = 5 := by norm_num
    rw [e9, e5]
    exact mulIndep_nine_five

/-- In the `c₁` form `Λ = 0` does occur: `x₁/y₁ = 9`, `x₂/y₂ = 81`, `b₁ = 2`, `b₂ = 1` (`g = 1`, `A₁ = 9`, `A₂ = 81`)
satisfy `Hyps 8 4`, and `Λ = 9² − 81 = 0`. The original defines `v_m(Λ)` only for `Λ ≠ 0`, so `Λ ≠ 0` is a premise. -/
theorem lam_zero_case :
    Hyps 8 4 9 1 81 1 1 2 1 9 81 ∧ ((9 : ℤ) / (1 : ℤ) : ℚ) ^ 2 - ((81 : ℤ) / (1 : ℤ) : ℚ) ^ 1 = 0 := by
  refine ⟨?_, by norm_num⟩
  simp only [Hyps, primeFactors_eight, Finset.mem_singleton, forall_eq,
    Finset.prod_singleton, factorization_eight_two]
  norm_num
  exact ⟨by decide, ⟨pvr_zero_of_not_dvd 2 9 9 (by norm_num) (by norm_num),
    pvr_zero_of_not_dvd 2 81 81 (by norm_num) (by norm_num)⟩,
    ⟨vpGe_of_dvd 2 8 3 8 (by norm_num) (by norm_num) (by norm_num),
      vpGe_of_dvd 2 80 1 80 (by norm_num) (by norm_num) (by norm_num)⟩,
    ⟨vpGe_of_dvd 2 8 2 8 (by norm_num) (by norm_num) (by norm_num),
      vpGe_of_dvd 2 80 2 80 (by norm_num) (by norm_num) (by norm_num)⟩,
    ⟨Real.log_nonneg (by norm_num), Real.log_le_log (by norm_num) (by norm_num)⟩,
    Real.log_nonneg (by norm_num), Real.log_le_log (by norm_num) (by norm_num)⟩

end Bugeaud

end Collatz.M1
