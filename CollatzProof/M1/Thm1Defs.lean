import CollatzProof.M1.BugeaudBridge

/-!
# Transcription of Theorem 1 of Bugeaud (2002) (`g = 1`, general `m`; Appendix B.1 of the paper)

Y. Bugeaud, *Linear forms in two m-adic logarithms and applications to Diophantine problems*,
Compositio Math. **132** (2002), 137–158, §2, Theorem 1 (p. 139, checked against the typeset pages of the original paper),
is stated **for general `m` and `g = 1`** as the proposition `Thm1G1 m`. Restricting to `g = 1` is a specialization of the original, so it is not stronger than the original.
Notation, valuations, (H1) and (H2) are written in the same way as in `BugeaudBridge.lean` (the transcription of Theorem 2).

**Correspondence between the statement of the original (pp. 138–139) and Lean**:
- Setting (p. 138): `m > 1` is an integer, `m = p₁^{u₁}⋯p_w^{u_w}`. The `p_i` are the elements of `m.primeFactors`, `u_i = m.factorization p_i`,
  `w = m.primeFactors.card`. `x₁/y₁`, `x₂/y₂` are nonzero rational numbers with `x₁/y₁ ≠ ±1`, `b₁`, `b₂` are positive integers,
  `Λ = (x₁/y₁)^{b₁} − (x₂/y₂)^{b₂}`, and `v_{p_i}(x₁/y₁) = v_{p_i}(x₂/y₂) = 0` for all `i` (pp. 138–139).
- (H1), (H2) (p. 139): a positive integer `g` coprime to `p₁⋯p_w` with `v_{p_i}((x₁/y₁)^g − 1) ≥ u_i`, `v_{p_i}((x₂/y₂)^g − 1) ≥ 1`, and,
  if `2 ∣ m`, `v₂((x_i/y_i)^g − 1) ≥ 2`. Here `g = 1` (`H1 m 1`, `H2 m 1`; `g = 1` is coprime to `p₁⋯p_w`).
- Theorem 1 (p. 139): `K ≥ 3`, `L ≥ 2`, `R₁, R₂, S₁, S₂` are positive integers, `R = R₁ + R₂ − 1`, `S = S₁ + S₂ − 1`, `N = KL`,
  `γ₁ = (R + g − 1)/(2R) − gN/(6R(S + g − 1))`, `γ₂ = (S + g − 1)/(2S) − gN/(6S(R + g − 1))` (`gam1`, `gam2`, with `g = 1` substituted).
  `p_i^{h_i}` is the largest power of `p_i` dividing both `b₁` and `b₂` (`hExp`, `hExp_spec`), and `p_i ∤ b₂/p_i^{h_i}` is assumed.
  `h = max_i h_i` (`hMax`). `b = ((R − 1)b₂ + (S − 1)b₁)/2 · (∏_{k=1}^{K−1} k!)^{−2/(K²−K)}` (`bB`).
  There are residue classes `c₁, c₂` modulo `g` with `Card{(x₁/y₁)^r(x₂/y₂)^s ; 0 ≤ r < R₁, 0 ≤ s < S₁, m₁r + m₂s ≡ c₁ (mod g)} ≥ L` and
  `Card{rb₂ + sb₁ ; 0 ≤ r < R₂, 0 ≤ s < S₂, m₁r + m₂s ≡ c₂ (mod g)} > (K − 1)L`. For `g = 1` the congruence conditions are void (`set1`, `set2`).
  Condition (1): if `K(L − 1) log m − (1 + 2w) log N − (K − 1) log b − γ₁LR h(x₁/y₁) − γ₂LS h(x₂/y₂) > 0` (`cond1`), then
  `v_m(Λ) < KL + h − 1/2`.
- `log` is the natural logarithm (as the `e^{3/2}` on p. 145 of the original shows). `v_m` is `BugeaudBridge.vm` (`v_m(a) − v_m(b)` for `a/b` in lowest terms, p. 138).

**Reading of the last two terms of (1)**: the original is typeset `γ₁LR max{|x₁|, |y₁|}`, `γ₂LS max{|x₂|, |y₂|}`, with the `log` missing (a misprint).
The same omission occurs, in the same form, in the inequality (2) of the proof (the last display on p. 142) and in the display `a_i = log A_i/log m ≥ max{|x_i|/log m, …}` (p. 143).
We read all three with the logarithmic heights `log max{|x_i|, |y_i|}` (`logHt`). Reasons: (i) (2) is obtained by applying Lemma 1 (p. 142), whose bound is in terms of the
logarithmic height `h(a/b) = log max{|a|, |b|}` defined just before it; applied correctly, it gives (2) with `h(x_i/y_i)`, and combining this with (3) and dividing by `N`
(p. 143: "Combining (2) and (3) and dividing by N, we see that (1) cannot hold") gives exactly the negation of (1) with logarithmic heights.
(ii) From `log A_i ≥ max{log|x_i|, log|y_i|, log m}` on p. 140, the display for `a_i` on p. 143 holds only with the logarithms, and the remark "(4) implies (1)" (p. 143),
through which Theorems 2 and 3 are derived, holds only for (1) with logarithmic heights. (iii) The remark on p. 140 that for an odd prime `m`, (1) is the same as (2) of [8], and
(2) of Bugeaud–Laurent (1996) (p. 314) is written with the logarithmic heights `h(α_i)`. Since `max ≥ log max`, the literal (1) is harder to satisfy, and the literal theorem is a
weaker theorem that follows from the version with logarithms; the proof in the original establishes the version with logarithms, and Theorems 2 and 3 are derived from it
(Section 15.4 of the paper; the reading was checked against the primary source in two independent reviews).
**Note.** Compared with the literal typesetting (without `log`), condition (1) with `log` is easier to satisfy, so the theorem is **stronger**. This transcription relies on
this reading of the misprint (the reading adopted in the paper).

**Choices made in the Lean statement** (none of them strengthens the original statement; each is weaker or equivalent):
1. Restriction to `g = 1` (a specialization).
2. `x_i, y_i` are nonzero integers (the original does not require lowest terms). The height is `log max{|x_i|, |y_i|}` of the given representation. The form `Thm1G1Red`,
   written with the height `h(x_i/y_i)` of the representation in lowest terms (`ratHt`, the definition on p. 142), is shown to be **equivalent** (`thm1G1_iff_red`)
   (the cardinality conditions imply `γ₁, γ₂ > 0` (`gam_pos_of_prem`), and the left-hand side of (1) is decreasing in the heights).
3. `v_p(z) ≥ k` is `VpGe` (with the convention `v_p(0) = +∞`, as in `BugeaudBridge`).
4. `Λ ≠ 0` is a premise. The original defines `v_m(Λ)` only for nonzero rational numbers (the value `vm m 0 = 0` is never used).
   In addition, `x₂/y₂ ≠ 1` is a premise (weaker than the original). If `x₂/y₂ = 1`, the valuation `v_p(x₂/y₂ − 1)` in (H1) and (H2) is `v_p(0)`,
   and one would rely on the convention `v_p(0) = +∞` of `VpGe` (p. 138 of the original says that the case `α₂ = ±1` is included, and Bugeaud–Laurent (1996)
   write the condition as `α_i^g ∈ U¹`, which contains 1, so the convention agrees with the original; with the extra premise nothing depends on it; suggested in an independent review).
   The application (Proposition 13.2B; Proposition 15.5 of the paper) treats the case `x₂/y₂ = 1` separately (`hgt_thm1` in `S13B.lean`).
5. The `>` and `≥` of the cardinality conditions and `(K − 1)L` are written in natural numbers (`K ≥ 3`, so the subtraction `K − 1` is not truncated).
6. The logarithm of `b`: `Real.log` returns 0 for arguments `≤ 0`, but the cardinality condition `Card{rb₂ + sb₁} > (K − 1)L ≥ 4` gives `R₂S₂ ≥ 5`,
   hence `R₂ ≥ 2` or `S₂ ≥ 2`, `(R − 1)b₂ + (S − 1)b₁ > 0` and `b > 0` (`bB_pos_of_prem`). Since `N = KL ≥ 6`, `m > 1` and the `max` in the heights is `≥ 1`, the other `log`s are also applied to positive numbers only.
-/

namespace Collatz.M1

namespace Bugeaud

open Real

/-! ## Notation -/

/-- The logarithmic height `log max{|x|, |y|}` of a pair of integers `(x, y)` (a representation of `x/y`) (the last two terms of (1), read with the `log` missing in the typesetting of the original). -/
noncomputable def logHt (x y : ℤ) : ℝ := Real.log (max |(x : ℝ)| |(y : ℝ)|)

/-- The logarithmic height `h(a/b) = log max{|a|, |b|}` of a rational number (`a`, `b` coprime; p. 142 of the original). -/
noncomputable def ratHt (r : ℚ) : ℝ := logHt r.num r.den

/-- `h_i`: the largest exponent of a power of `p` dividing both `b₁` and `b₂` (`hExp_spec`). -/
def hExp (p b₁ b₂ : ℕ) : ℕ := padicValNat p (Nat.gcd b₁ b₂)

/-- `h = max_{1 ≤ i ≤ w} h_i`. -/
def hMax (m b₁ b₂ : ℕ) : ℕ := m.primeFactors.sup (fun p => hExp p b₁ b₂)

/-- `γ₁ = (R + g − 1)/(2R) − gN/(6R(S + g − 1))` (p. 139). -/
noncomputable def gam1 (g R S N : ℝ) : ℝ := (R + g - 1) / (2 * R) - g * N / (6 * R * (S + g - 1))

/-- `γ₂ = (S + g − 1)/(2S) − gN/(6S(R + g − 1))` (p. 139). -/
noncomputable def gam2 (g R S N : ℝ) : ℝ := (S + g - 1) / (2 * S) - g * N / (6 * S * (R + g - 1))

/-- `∏_{k=1}^{K−1} k!`. -/
noncomputable def factProd (K : ℕ) : ℝ := ∏ k ∈ Finset.Icc 1 (K - 1), ((k.factorial : ℕ) : ℝ)

/-- `b = ((R − 1)b₂ + (S − 1)b₁)/2 · (∏_{k=1}^{K−1} k!)^{−2/(K²−K)}` (p. 139; `R`, `S` are passed as `R₁ + R₂ − 1`, `S₁ + S₂ − 1`). -/
noncomputable def bB (K R S b₁ b₂ : ℕ) : ℝ :=
  (((R : ℝ) - 1) * b₂ + ((S : ℝ) - 1) * b₁) / 2 * factProd K ^ ((-2 : ℝ) / ((K : ℝ) ^ 2 - K))

/-- `{(x₁/y₁)^r (x₂/y₂)^s ; 0 ≤ r < R₁, 0 ≤ s < S₁}` (the congruence condition is void since `g = 1`). -/
def set1 (r₁ r₂ : ℚ) (R₁ S₁ : ℕ) : Finset ℚ :=
  (Finset.range R₁ ×ˢ Finset.range S₁).image (fun rs => r₁ ^ rs.1 * r₂ ^ rs.2)

/-- `{r b₂ + s b₁ ; 0 ≤ r < R₂, 0 ≤ s < S₂}` (the congruence condition is void since `g = 1`). -/
def set2 (b₁ b₂ R₂ S₂ : ℕ) : Finset ℕ :=
  (Finset.range R₂ ×ˢ Finset.range S₂).image (fun rs => rs.1 * b₂ + rs.2 * b₁)

/-- The left-hand side of condition (1) (`g = 1`): `K(L − 1) log m − (1 + 2w) log N − (K − 1) log b − γ₁LR H₁ − γ₂LS H₂`.
The arguments `H₁`, `H₂` are the logarithmic heights of `x₁/y₁`, `x₂/y₂`. -/
noncomputable def cond1 (m : ℕ) (H₁ H₂ : ℝ) (b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ) : ℝ :=
  (K : ℝ) * ((L : ℝ) - 1) * Real.log m
    - (1 + 2 * (m.primeFactors.card : ℝ)) * Real.log ((K * L : ℕ) : ℝ)
    - ((K : ℝ) - 1) * Real.log (bB K (R₁ + R₂ - 1) (S₁ + S₂ - 1) b₁ b₂)
    - gam1 1 ((R₁ + R₂ - 1 : ℕ) : ℝ) ((S₁ + S₂ - 1 : ℕ) : ℝ) ((K * L : ℕ) : ℝ) * L
        * ((R₁ + R₂ - 1 : ℕ) : ℝ) * H₁
    - gam2 1 ((R₁ + R₂ - 1 : ℕ) : ℝ) ((S₁ + S₂ - 1 : ℕ) : ℝ) ((K * L : ℕ) : ℝ) * L
        * ((S₁ + S₂ - 1 : ℕ) : ℝ) * H₂

/-- (H1) (p. 139): `v_{p_i}(r₁^g − 1) ≥ u_i` and `v_{p_i}(r₂^g − 1) ≥ 1` for all `i`. -/
def H1 (m g : ℕ) (r₁ r₂ : ℚ) : Prop :=
  ∀ p ∈ m.primeFactors, VpGe p (r₁ ^ g - 1) (m.factorization p) ∧ VpGe p (r₂ ^ g - 1) 1

/-- (H2) (p. 139): if `2 ∣ m`, then `v₂(r₁^g − 1) ≥ 2` and `v₂(r₂^g − 1) ≥ 2`. -/
def H2 (m g : ℕ) (r₁ r₂ : ℚ) : Prop :=
  2 ∣ m → VpGe 2 (r₁ ^ g - 1) 2 ∧ VpGe 2 (r₂ ^ g - 1) 2

/-- The premises of Theorem 1 other than (1) and `Λ ≠ 0` (`g = 1`; `r_i = x_i/y_i`). -/
def Prem (m : ℕ) (r₁ r₂ : ℚ) (b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ) : Prop :=
  -- Setting (p. 138): `m > 1`, `x₁/y₁`, `x₂/y₂` are nonzero rational numbers with `x₁/y₁ ≠ ±1`, and `b₁`, `b₂` are positive integers.
  -- `r₂ ≠ 1` is not a premise of the original; it was added to weaken the statement (so that nothing depends on the convention `v_p(0) = +∞`; suggested in an independent review)
  1 < m ∧ r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ r₁ ≠ 1 ∧ r₁ ≠ -1 ∧ r₂ ≠ 1 ∧ 0 < b₁ ∧ 0 < b₂ ∧
  -- `v_{p_i}(x₁/y₁) = v_{p_i}(x₂/y₂) = 0` for all `i` (pp. 138–139)
  (∀ p ∈ m.primeFactors, padicValRat p r₁ = 0 ∧ padicValRat p r₂ = 0) ∧
  -- (H1), (H2) with `g = 1` (p. 139)
  H1 m 1 r₁ r₂ ∧ H2 m 1 r₁ r₂ ∧
  -- Theorem 1: `K ≥ 3`, `L ≥ 2`, and `R₁, R₂, S₁, S₂` are positive integers
  3 ≤ K ∧ 2 ≤ L ∧ 0 < R₁ ∧ 0 < R₂ ∧ 0 < S₁ ∧ 0 < S₂ ∧
  -- `p_i` does not divide `b₂/p_i^{h_i}`
  (∀ p ∈ m.primeFactors, ¬ p ∣ b₂ / p ^ hExp p b₁ b₂) ∧
  -- the cardinality conditions (`g = 1`)
  L ≤ (set1 r₁ r₂ R₁ S₁).card ∧ (K - 1) * L < (set2 b₁ b₂ R₂ S₂).card

/-! ## Theorem 1 of the original (`g = 1`) -/

/-- **Theorem 1 of the original** (`g = 1`, for a fixed `m`). `x_i/y_i` is the quotient of a pair of nonzero integers, and the height is
`log max{|x_i|, |y_i|}` of the given representation. -/
def Thm1G1 (m : ℕ) : Prop :=
  ∀ (x₁ y₁ x₂ y₂ : ℤ) (b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ),
    x₁ ≠ 0 → y₁ ≠ 0 → x₂ ≠ 0 → y₂ ≠ 0 →
    Prem m (x₁ / y₁ : ℚ) (x₂ / y₂ : ℚ) b₁ b₂ K L R₁ R₂ S₁ S₂ →
    0 < cond1 m (logHt x₁ y₁) (logHt x₂ y₂) b₁ b₂ K L R₁ R₂ S₁ S₂ →
    (x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂ ≠ 0 →
    (vm m ((x₁ / y₁ : ℚ) ^ b₁ - (x₂ / y₂ : ℚ) ^ b₂) : ℝ) < K * L + hMax m b₁ b₂ - 1 / 2

/-- The same theorem, written with rational numbers `r_i = x_i/y_i` and the heights `h(r_i)` in lowest terms (`ratHt`, p. 142). Equivalent to `Thm1G1` by `thm1G1_iff_red`. -/
def Thm1G1Red (m : ℕ) : Prop :=
  ∀ (r₁ r₂ : ℚ) (b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ),
    Prem m r₁ r₂ b₁ b₂ K L R₁ R₂ S₁ S₂ →
    0 < cond1 m (ratHt r₁) (ratHt r₂) b₁ b₂ K L R₁ R₂ S₁ S₂ →
    r₁ ^ b₁ - r₂ ^ b₂ ≠ 0 →
    (vm m (r₁ ^ b₁ - r₂ ^ b₂) : ℝ) < K * L + hMax m b₁ b₂ - 1 / 2

/-- Theorem 1 of the original (`g = 1`) in full (for all `m`). -/
def Thm1G1All : Prop := ∀ m : ℕ, Thm1G1 m

/-! ## Properties of the notation (for checking the transcription) -/

/-- `hExp` is "the largest exponent of a power of `p` dividing both `b₁` and `b₂`": `p^k ∣ b₁ ∧ p^k ∣ b₂ ↔ k ≤ hExp p b₁ b₂` (`b₁ > 0`). -/
theorem hExp_spec {p b₁ b₂ : ℕ} [Fact p.Prime] (hb₁ : 0 < b₁) (k : ℕ) :
    p ^ k ∣ b₁ ∧ p ^ k ∣ b₂ ↔ k ≤ hExp p b₁ b₂ := by
  rw [← Nat.dvd_gcd_iff]
  exact padicValNat_dvd_iff_le (Nat.gcd_pos_of_pos_left b₂ hb₁).ne'

/-- If `b₂ = 1`, then `h_i = 0`. -/
theorem hExp_one (p b₁ : ℕ) : hExp p b₁ 1 = 0 := by
  simp [hExp]

/-- If `b₂ = 1`, then `h = 0`. -/
theorem hMax_one (m b₁ : ℕ) : hMax m b₁ 1 = 0 := by
  unfold hMax
  exact (Finset.sup_eq_bot_iff _ _).2 (fun p _ => hExp_one p b₁)

/-- The height of `x/y` in lowest terms is at most the height of the representation `(x, y)` (`x, y ≠ 0`). -/
theorem ratHt_le_logHt {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) : ratHt (x / y : ℚ) ≤ logHt x y := by
  have hdiv : ((x : ℚ) / (y : ℚ)) = Rat.divInt x y := Rat.intCast_div_eq_divInt x y
  have hnum : |((x / y : ℚ)).num| ≤ |x| := by
    have h1 : ((x / y : ℚ)).num ∣ x := by rw [hdiv]; exact Rat.num_dvd x hy
    exact Int.le_of_dvd (abs_pos.2 hx) ((abs_dvd_abs _ _).2 h1)
  have hden : (((x / y : ℚ)).den : ℤ) ≤ |y| := by
    have h1 : (((x / y : ℚ)).den : ℤ) ∣ y := by rw [hdiv]; exact Rat.den_dvd x y
    exact Int.le_of_dvd (abs_pos.2 hy) ((dvd_abs _ _).2 h1)
  have hnum' : |(((x / y : ℚ)).num : ℝ)| ≤ |(x : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast hnum
  have hden' : |((((x / y : ℚ)).den : ℤ) : ℝ)| ≤ |(y : ℝ)| := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _), ← Int.cast_abs]
    exact_mod_cast hden
  have hpos : 0 < max |((((x / y : ℚ)).num : ℤ) : ℝ)| |((((x / y : ℚ)).den : ℤ) : ℝ)| := by
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast ((x / y : ℚ)).den_pos
  unfold ratHt logHt
  exact Real.log_le_log hpos (max_le_max hnum' hden')

/-- The height of the representation `(r.num, r.den)` is `ratHt r`. -/
theorem logHt_num_den (r : ℚ) : logHt r.num (r.den : ℤ) = ratHt r := rfl

/-- `Card{rb₂ + sb₁ ; r < R₂, s < S₂} ≤ R₂S₂` (together with the cardinality condition, `R₂S₂ > (K − 1)L`). -/
theorem card_set2_le (b₁ b₂ R₂ S₂ : ℕ) : (set2 b₁ b₂ R₂ S₂).card ≤ R₂ * S₂ := by
  unfold set2
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- `∏_{k=1}^{K−1} k! > 0`. -/
theorem factProd_pos (K : ℕ) : 0 < factProd K :=
  Finset.prod_pos (fun k _ => by exact_mod_cast Nat.factorial_pos k)

/-- The premises give `b > 0` (`R₂S₂ > (K − 1)L ≥ 4`, so `R₂ ≥ 2` or `S₂ ≥ 2`; `Real.log b` is applied to positive numbers only). -/
theorem bB_pos_of_prem {m : ℕ} {r₁ r₂ : ℚ} {b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ}
    (h : Prem m r₁ r₂ b₁ b₂ K L R₁ R₂ S₁ S₂) : 0 < bB K (R₁ + R₂ - 1) (S₁ + S₂ - 1) b₁ b₂ := by
  obtain ⟨-, -, -, -, -, -, hb₁, hb₂, -, -, -, hK, hL, hR₁, hR₂, hS₁, hS₂, -, -, hc2⟩ := h
  have hc := lt_of_lt_of_le hc2 (card_set2_le b₁ b₂ R₂ S₂)
  have h4 : 4 ≤ (K - 1) * L := by
    calc 4 = 2 * 2 := rfl
      _ ≤ (K - 1) * L := Nat.mul_le_mul (by omega) hL
  have h2 : 2 ≤ R₂ ∨ 2 ≤ S₂ := by
    rcases Nat.lt_or_ge R₂ 2 with hr | hr
    · rcases Nat.lt_or_ge S₂ 2 with hs | hs
      · have e1 : R₂ = 1 := by omega
        have e2 : S₂ = 1 := by omega
        rw [e1, e2] at hc; omega
      · exact Or.inr hs
    · exact Or.inl hr
  have hb₁r : (1 : ℝ) ≤ b₁ := by exact_mod_cast hb₁
  have hb₂r : (1 : ℝ) ≤ b₂ := by exact_mod_cast hb₂
  have hX : 0 < (((R₁ + R₂ - 1 : ℕ) : ℝ) - 1) * b₂ + (((S₁ + S₂ - 1 : ℕ) : ℝ) - 1) * b₁ := by
    rcases h2 with hr | hs
    · have hR : (2 : ℝ) ≤ ((R₁ + R₂ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ R₁ + R₂ - 1)
      have hS : (1 : ℝ) ≤ ((S₁ + S₂ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ S₁ + S₂ - 1)
      nlinarith
    · have hR : (1 : ℝ) ≤ ((R₁ + R₂ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ R₁ + R₂ - 1)
      have hS : (2 : ℝ) ≤ ((S₁ + S₂ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ S₁ + S₂ - 1)
      nlinarith
  unfold bB
  exact mul_pos (div_pos hX two_pos) (Real.rpow_pos_of_pos (factProd_pos K) _)

/-- The premises give `γ₁ > 0` and `γ₂ > 0` (`g = 1`; `3RS ≥ 3R₂S₂ > 3(K − 1)L ≥ KL`). -/
theorem gam_pos_of_prem {m : ℕ} {r₁ r₂ : ℚ} {b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ}
    (h : Prem m r₁ r₂ b₁ b₂ K L R₁ R₂ S₁ S₂) :
    0 < gam1 1 ((R₁ + R₂ - 1 : ℕ) : ℝ) ((S₁ + S₂ - 1 : ℕ) : ℝ) ((K * L : ℕ) : ℝ) ∧
      0 < gam2 1 ((R₁ + R₂ - 1 : ℕ) : ℝ) ((S₁ + S₂ - 1 : ℕ) : ℝ) ((K * L : ℕ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hK, hL, hR₁, hR₂, hS₁, hS₂, -, -, hc2⟩ := h
  have hc := lt_of_lt_of_le hc2 (card_set2_le b₁ b₂ R₂ S₂)
  -- `KL < 3 R S` (natural numbers)
  have hRS : R₂ * S₂ ≤ (R₁ + R₂ - 1) * (S₁ + S₂ - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hKL : K * L < 3 * ((R₁ + R₂ - 1) * (S₁ + S₂ - 1)) := by
    have h1 : K * L ≤ 3 * ((K - 1) * L) := by
      have : K ≤ 3 * (K - 1) := by omega
      calc K * L ≤ (3 * (K - 1)) * L := Nat.mul_le_mul_right L this
        _ = 3 * ((K - 1) * L) := by ring
    omega
  have hR : (0 : ℝ) < ((R₁ + R₂ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R₁ + R₂ - 1)
  have hS : (0 : ℝ) < ((S₁ + S₂ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < S₁ + S₂ - 1)
  have hKLr : ((K * L : ℕ) : ℝ) < 3 * (((R₁ + R₂ - 1 : ℕ) : ℝ) * ((S₁ + S₂ - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hKL
  set R : ℝ := ((R₁ + R₂ - 1 : ℕ) : ℝ)
  set S : ℝ := ((S₁ + S₂ - 1 : ℕ) : ℝ)
  set N : ℝ := ((K * L : ℕ) : ℝ)
  have key : 0 < 1 / 2 - N / (6 * R * S) := by
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith
  constructor
  · have : gam1 1 R S N = 1 / 2 - N / (6 * R * S) := by
      unfold gam1
      rw [show R + 1 - 1 = R by ring, show S + 1 - 1 = S by ring, one_mul]
      field_simp
    rw [this]; exact key
  · have : gam2 1 R S N = 1 / 2 - N / (6 * R * S) := by
      unfold gam2
      rw [show R + 1 - 1 = R by ring, show S + 1 - 1 = S by ring, one_mul]
      field_simp
    rw [this]; exact key

/-- The left-hand side of (1) is decreasing in the heights (under the premises, `γ₁, γ₂ > 0`). -/
theorem cond1_anti {m : ℕ} {r₁ r₂ : ℚ} {b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ}
    (h : Prem m r₁ r₂ b₁ b₂ K L R₁ R₂ S₁ S₂) {H₁ H₂ H₁' H₂' : ℝ} (h₁ : H₁ ≤ H₁') (h₂ : H₂ ≤ H₂') :
    cond1 m H₁' H₂' b₁ b₂ K L R₁ R₂ S₁ S₂ ≤ cond1 m H₁ H₂ b₁ b₂ K L R₁ R₂ S₁ S₂ := by
  obtain ⟨g1, g2⟩ := gam_pos_of_prem h
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hR : (0 : ℝ) ≤ ((R₁ + R₂ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hS : (0 : ℝ) ≤ ((S₁ + S₂ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold cond1
  have e1 := mul_le_mul_of_nonneg_left h₁ (mul_nonneg (mul_nonneg g1.le hL) hR)
  have e2 := mul_le_mul_of_nonneg_left h₂ (mul_nonneg (mul_nonneg g2.le hL) hS)
  nlinarith [e1, e2]

/-- **Equivalence**: the form written with the heights of the given representations (`Thm1G1`) and the form written with the heights in lowest terms (`Thm1G1Red`) are the same proposition.
(`→`: insert the representation `(r.num, r.den)`. `←`: the left-hand side of (1) is decreasing in the heights, and the height of a representation is at least the height in lowest terms.) -/
theorem thm1G1_iff_red (m : ℕ) : Thm1G1 m ↔ Thm1G1Red m := by
  constructor
  · intro h r₁ r₂ b₁ b₂ K L R₁ R₂ S₁ S₂ hP hc hΛ
    have e₁ : ((r₁.num : ℚ) / ((r₁.den : ℤ) : ℚ)) = r₁ := num_div_den' r₁
    have e₂ : ((r₂.num : ℚ) / ((r₂.den : ℤ) : ℚ)) = r₂ := num_div_den' r₂
    have hP' := hP
    obtain ⟨-, hr₁, hr₂, -⟩ := hP'
    have key := h r₁.num r₁.den r₂.num r₂.den b₁ b₂ K L R₁ R₂ S₁ S₂
      (Rat.num_ne_zero.2 hr₁) (by exact_mod_cast r₁.den_nz) (Rat.num_ne_zero.2 hr₂)
      (by exact_mod_cast r₂.den_nz) (by rw [e₁, e₂]; exact hP)
      (by rw [logHt_num_den, logHt_num_den]; exact hc) (by rw [e₁, e₂]; exact hΛ)
    rwa [e₁, e₂] at key
  · intro h x₁ y₁ x₂ y₂ b₁ b₂ K L R₁ R₂ S₁ S₂ hx₁ hy₁ hx₂ hy₂ hP hc hΛ
    refine h _ _ b₁ b₂ K L R₁ R₂ S₁ S₂ hP ?_ hΛ
    exact lt_of_lt_of_le hc (cond1_anti hP (ratHt_le_logHt hx₁ hy₁) (ratHt_le_logHt hx₂ hy₂))

end Bugeaud

end Collatz.M1
