# A strict improvement of the Terras-type bound for integers with long Collatz stopping times

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22986641.svg)](https://doi.org/10.5281/zenodo.22986641)

This repository contains the Lean 4 formalization accompanying the preprint *A strict improvement of the
Terras-type bound for integers with long Collatz stopping times* by Hiroyuki Nashida (Zenodo, 2026,
doi:[10.5281/zenodo.22986641](https://doi.org/10.5281/zenodo.22986641)). It formalizes, with Mathlib, the main
theorem of the paper (for every $\alpha \in (1/2, 0.659]$ some $\varepsilon > 0$ lowers the Terras-type exponent
$\alpha(1-c)$ for integers with coefficient stopping time larger than $K$), its version for the stopping time, and
the corollary on integers whose orbit never drops below the starting value, both in qualitative form and with the
explicit values $\varepsilon(0.6) = 2.46 \times 10^{-11}$ and $1 - c - 5.84 \times 10^{-11}$. Theorem 1 of Bugeaud
(2002), in the case $g = 1$, enters as an explicit hypothesis. The formal proofs of revision r6, which assume
Theorem 2 of Bugeaud (2002) instead, are kept.

## Paper

- **Author:** Hiroyuki Nashida
- **Title:** A strict improvement of the Terras-type bound for integers with long Collatz stopping times
- **Preprint:** Zenodo, 2026
- **DOI:** [10.5281/zenodo.22986641](https://doi.org/10.5281/zenodo.22986641)
- **Lean formalization:** this repository

Revision r7 (September 28, 2026). This repository accompanies revision r7 of the paper; the revision number is
incremented with every revision of the paper and of this repository.

## Abstract

Let $T$ be the shortcut Collatz map and $c = 1 - H(1/\log_2 3) = 0.05004\ldots$, where $H$ is the binary
entropy. The Terras bijection between residues modulo $2^K$ and parity words shows that at most
$2^{\alpha(1-c)K + o(K)}$ integers $n \le 2^{\alpha K}$ have coefficient stopping time larger than $K$; we call
this the Terras-type bound. We prove that for every $\alpha \in (1/2, 0.659]$ this exponent can be lowered: there
is $\varepsilon(\alpha) > 0$ such that the number of such $n$ is at most $2^{(\alpha(1-c) - \varepsilon)K}$ for all
large $K$, and the same holds for the ordinary stopping time. Consequently, for some $\varepsilon > 0$, at most
$x^{1-c-\varepsilon}$ integers $n \le x$ have an orbit that never drops below $n$. The proof reduces the count,
through a bilinear inequality and a decomposition of the frequencies into shells, to a lower bound for the heights
of the lattices $\lbrace (n,m) : m \equiv 3^L n \pmod{2^N} \rbrace$; this is the only place where an external
theorem is used, namely Bugeaud's bound for linear forms in two $m$-adic logarithms (Compositio Math. 2002,
Theorem 1, with $m = 8$; Theorem 2 there suffices for the qualitative statements). For example
$\varepsilon(0.6) = 2.46 \times 10^{-11}$, and the exponent for orbits that never drop below their starting value is
$1 - c - 5.84 \times 10^{-11}$, which improves the exponent of Theorem F in Lagarias's 1985 survey.

*What is verified and how.* The main statements, both in qualitative form and with the explicit values
$2.46 \times 10^{-11}$ and $5.84 \times 10^{-11}$, are formalized in Lean 4. Bugeaud's Theorem 1 (for $g = 1$)
enters the formalization as an explicit hypothesis, transcribed from the published statement (whose condition (1) we
read with logarithmic heights, correcting a misprint) and compared with the primary source; apart from this
hypothesis only the three axioms used throughout Mathlib appear. The numerical inequalities of the written proof
(246 of them) have in addition been checked with rigorous interval arithmetic in exact rational numbers. The Lean
code is available in this repository.

## Main results in Lean

The formalized statements are Theorem 1.1, Theorem 1.2 and Corollary 1.3 of the paper, in qualitative form
(existence of some $\varepsilon > 0$) and with explicit values. Output of `#check` in `verify/Probe.lean`
(`verify/probe-2026-09-28.log`). Lean prints the decimal literals `2.46e-11`, `5.84e-11`, `5.35e-14` and `1.33e-13`
of the source as `246e-13`, `584e-13`, `535e-16` and `133e-15`.

Under Theorem 1 of Bugeaud (2002), the hypothesis `Thm1G1 8` (revision r7):

```lean
Collatz.M1.m1_main_thm1 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
  ∃ ε > 0, ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.NKcount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
Collatz.M1.m1_v3 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) (α : ℝ) (hα : 0.5114 ≤ α) (hα' : α ≤ 0.659) (ε : ℝ)
  (hε : ε < 2.18 * Collatz.M1.deltaV3 ^ 2 * (1 - α)) :
  ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.NKcount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
Collatz.M1.m1_v3_06 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) :
  ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.NKcount K ⌊2 ^ (0.6 * ↑K)⌋₊) ≤ 2 ^ ((0.6 * (1 - Collatz.M1.cc) - 246e-13) * ↑K)
CollatzND.m1_sigma_thm1 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
  ∃ ε > 0, ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.SigmaCount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
CollatzND.m1_sigma_v3 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) (α : ℝ) (hα : 0.5114 ≤ α) (hα' : α ≤ 0.659) (ε : ℝ)
  (hε : ε < 2.18 * Collatz.M1.deltaV3 ^ 2 * (1 - α)) :
  ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.SigmaCount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
CollatzND.m1_sigma_v3_06 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) :
  ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.SigmaCount K ⌊2 ^ (0.6 * ↑K)⌋₊) ≤ 2 ^ ((0.6 * (1 - Collatz.M1.cc) - 246e-13) * ↑K)
CollatzND.m1_divergent_thm1 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) :
  ∃ ε > 0, ∃ x0, ∀ x ≥ x0, ↑(Collatz.M1.DivCount x) ≤ ↑x ^ (1 - Collatz.M1.cc - ε)
CollatzND.m1_divergent_v3 (hB1 : Collatz.M1.Bugeaud.Thm1G1 8) :
  ∃ x0, ∀ x ≥ x0, ↑(Collatz.M1.DivCount x) ≤ ↑x ^ (1 - Collatz.M1.cc - 584e-13)
```

Under Theorem 2 of Bugeaud (2002), the hypothesis `BugeaudHyp` (the statements of revision r6, and the explicit
values of revision r6, formalized since then):

```lean
Collatz.M1.m1_main (hBug : Collatz.M1.BugeaudHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
  ∃ ε > 0, ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.NKcount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
CollatzND.m1_sigma (hBug : Collatz.M1.BugeaudHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
  ∃ ε > 0, ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.SigmaCount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
CollatzND.m1_divergent (hBug : Collatz.M1.BugeaudHyp) :
  ∃ ε > 0, ∃ x0, ∀ x ≥ x0, ↑(Collatz.M1.DivCount x) ≤ ↑x ^ (1 - Collatz.M1.cc - ε)
Collatz.M1.m1_explicit_06 (hBug : Collatz.M1.BugeaudHyp) :
  ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.NKcount K ⌊2 ^ (0.6 * ↑K)⌋₊) ≤ 2 ^ ((0.6 * (1 - Collatz.M1.cc) - 535e-16) * ↑K)
CollatzND.m1_sigma_explicit_06 (hBug : Collatz.M1.BugeaudHyp) :
  ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.SigmaCount K ⌊2 ^ (0.6 * ↑K)⌋₊) ≤ 2 ^ ((0.6 * (1 - Collatz.M1.cc) - 535e-16) * ↑K)
CollatzND.m1_divergent_explicit (hBug : Collatz.M1.BugeaudHyp) :
  ∃ x0, ∀ x ≥ x0, ↑(Collatz.M1.DivCount x) ≤ ↑x ^ (1 - Collatz.M1.cc - 133e-15)
```

The definitions occurring in these statements, as printed by `#print` in `verify/Probe.lean` (the hypotheses
`Thm1G1`, `BugeaudHyp` and `RhinHyp` are printed in the section "The hypotheses" below):

```lean
def Collatz.T : ℕ → ℕ :=
fun n => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
def Collatz.M1.pw : ℕ → (len : ℕ) → Fin len → Bool :=
fun n len i => decide (Collatz.T^[↑i] n % 2 = 1)
def Collatz.M1.ones : {n : ℕ} → (Fin n → Bool) → ℕ → ℕ :=
fun {n} x j => {i | ↑i < j ∧ x i = true}.card
def Collatz.M1.lam : ℝ :=
Real.logb 2 3
def Collatz.M1.hw : {n : ℕ} → ℝ → (Fin n → Bool) → ℕ → ℝ :=
fun {n} y x j => y + Collatz.M1.lam * ↑(Collatz.M1.ones x j) - ↑j
def Collatz.M1.SurvW : {n : ℕ} → ℝ → (Fin n → Bool) → Prop :=
fun {n} y x => ∀ (j : ℕ), 1 ≤ j → j ≤ n → 0 ≤ Collatz.M1.hw y x j
def Collatz.M1.NKcount : ℕ → ℕ → ℕ :=
fun K X => {n ∈ Finset.Icc 1 X | Collatz.M1.SurvW 0 (Collatz.M1.pw n K)}.card
def Collatz.M1.Hb : ℝ → ℝ :=
fun ρ => -(ρ * Real.logb 2 ρ) - (1 - ρ) * Real.logb 2 (1 - ρ)
def Collatz.M1.rhoc : ℝ :=
1 / Collatz.M1.lam
def Collatz.M1.cc : ℝ :=
1 - Collatz.M1.Hb Collatz.M1.rhoc
def Collatz.M1.SigmaGt : ℕ → ℕ → Prop :=
fun n K => ∀ (j : ℕ), 1 ≤ j → j ≤ K → n ≤ Collatz.T^[j] n
def Collatz.M1.SigmaCount : ℕ → ℕ → ℕ :=
fun K X => {n ∈ Finset.Icc 1 X | Collatz.M1.SigmaGt n K}.card
def Collatz.M1.DivCount : ℕ → ℕ :=
fun X => {n ∈ Finset.Icc 1 X | ∀ (K : ℕ), Collatz.M1.SigmaGt n K}.card
def Collatz.M1.deltaV3 : ℝ :=
53116e-10
```

In words, with $T$ the shortcut map, $o_j(n)$ the number of odd terms among $n, T(n), \ldots, T^{j-1}(n)$,
$c = 1 - H(1/\log_2 3) \approx 0.050044$ ($H$ the binary entropy in bits) and $\delta = 5.3116 \times 10^{-6}$
(`deltaV3`):

- **`m1_main_thm1`** (Theorem 1.1, qualitative form). For every $\alpha \in (1/2, 0.659]$ there are
  $\varepsilon > 0$ and $K_0$ such that for all $K \ge K_0$ the number of $1 \le n \le 2^{\alpha K}$ with
  $3^{o_j(n)} \ge 2^j$ for all $1 \le j \le K$ (coefficient stopping time $> K$) is at most
  $2^{(\alpha(1-c) - \varepsilon)K}$. The Terras-type count gives the exponent $\alpha(1-c)$.
- **`m1_v3`**, **`m1_v3_06`** (Theorem 1.1 with explicit values). The same bound for every
  $\alpha \in [0.5114, 0.659]$ and every $\varepsilon < 2.18 \delta^2 (1 - \alpha)$; for $\alpha = 0.6$ this
  admits $\varepsilon = 2.46 \times 10^{-11}$ (since $2.18 \delta^2 \cdot 0.4 = 2.46018 \times 10^{-11}$).
- **`m1_sigma_thm1`**, **`m1_sigma_v3`**, **`m1_sigma_v3_06`** (Theorem 1.2). The same bounds for the number of
  $1 \le n \le 2^{\alpha K}$ with $T^j(n) \ge n$ for all $1 \le j \le K$ (stopping time $\sigma(n) > K$).
- **`m1_divergent_thm1`**, **`m1_divergent_v3`** (Corollary 1.3). For some $\varepsilon > 0$, respectively for
  $\varepsilon = 5.84 \times 10^{-11}$, and all sufficiently large $x$, the number of $1 \le n \le x$ with
  $\sigma(n) = \infty$ (that is, $T^j(n) \ge n$ for every $j \ge 1$) is at most $x^{1-c-\varepsilon}$. ($n = 1$ is
  counted, since $T(1) = 2$ and $T(2) = 1$.)
- **`m1_main`**, **`m1_sigma`**, **`m1_divergent`** and **`m1_explicit_06`**, **`m1_sigma_explicit_06`**,
  **`m1_divergent_explicit`**. The same statements under `BugeaudHyp` (Theorem 2 of Bugeaud), with the explicit
  values $\varepsilon(0.6) = 5.35 \times 10^{-14}$ and $1 - c - 1.33 \times 10^{-13}$ of revision r6.

The namespace `Collatz.M1` is named after an internal label of the project; it has no mathematical meaning. The
same label occurs in the directory `CollatzProof/M1/`, in the files `CollatzND/M1*.lean` and in the theorem names
`m1_main`, `m1_v3`, `m1_sigma`, `m1_divergent`, and so on. The suffix `v3` (`m1_v3`, `thmA_v3`, `ExplicitV3.lean`, ...)
refers to version 3 of the (Japanese) proof manuscript, whose constants are those of revision r7 of the paper;
`Explicit.lean`, `ExplicitCore.lean` and `ExplicitNum.lean` belong to version 2 (revision r6). The suffix `thm1`
(`m1_main_thm1`, `hgt_thm1`, ...) refers to Theorem 1 of Bugeaud (2002).

## What is and is not verified

The Lean kernel certifies that the statements above follow from their hypotheses (`Thm1G1 8`, respectively
`BugeaudHyp`) within Mathlib, using no axioms beyond the three that Mathlib uses throughout. It does not certify that
the statements express the intended mathematics, nor that the hypotheses agree with the published theorems; these
are matters of reading (see "What rests on the written proof or on reading" below).

### Checked by the Lean kernel

- The theorems of revision r7 displayed above, each as an implication `Thm1G1 8 → …`:
  `Collatz.M1.m1_main_thm1`, `Collatz.M1.m1_v3`, `Collatz.M1.m1_v3_06`, `CollatzND.m1_sigma_thm1`,
  `CollatzND.m1_sigma_v3`, `CollatzND.m1_sigma_v3_06`, `CollatzND.m1_divergent_thm1`, `CollatzND.m1_divergent_v3`;
  also `Collatz.M1.sigma_v3`, `sigma_v3_06`, `divergent_count_v3`, `sigma_main_thm1` and `divergent_count_thm1`
  (which take the Rhin-type bound `RhinHyp` as a further hypothesis).
- The theorems of revision r6, each as an implication `BugeaudHyp → …`: `Collatz.M1.m1_main`, `CollatzND.m1_sigma`,
  `CollatzND.m1_divergent`, and the explicit `Collatz.M1.m1_explicit_06`, `CollatzND.m1_sigma_explicit_06`,
  `CollatzND.m1_divergent_explicit` (and `Collatz.M1.sigma_main`, `divergent_count`, `sigma_explicit_06`,
  `divergent_count_explicit` under the further hypothesis `RhinHyp`); `CollatzND.rhinHyp_holds` proves `RhinHyp`.
- Proposition 15.5 of the paper from `Thm1G1 8` (`Collatz.M1.hgt_thm1`), the non-degeneracy of `Thm1G1 8`
  (`Collatz.M1.thm1G1_eight_premises_satisfiable`) and the equivalence with the form in lowest terms
  (`Collatz.M1.Bugeaud.thm1G1_iff_red`); see below.
- The bridge `Collatz.M1.Bugeaud.bugeaudHyp_of_thm2 : Thm2 8 4 → BugeaudHyp` from a Lean transcription of
  Bugeaud's Theorem 2 to the hypothesis `BugeaudHyp`.
- The specification tests of `CollatzProof/M1/Spec.lean` (see below).

Since revision r7 the constants of $R_\delta$ and of (WF) and the supply of the lattice condition are parameters of
general forms (`RdeltaG`, `WFG`, `HgtSupply`, `K_coreG`, `K_core_paramG`, `m1_mainG`, `C_thmAG`, `thmBG`, ...); the
declarations of revision r6 are specializations of these, and their statements are unchanged.

### The hypotheses `Thm1G1 8`, `BugeaudHyp` and `RhinHyp`

- **`Thm1G1 8` is an explicit hypothesis, not an axiom.** `Collatz.M1.Bugeaud.Thm1G1 m`
  (`CollatzProof/M1/Thm1Defs.lean`) is a Lean transcription of Theorem 1 of Y. Bugeaud, *Linear forms in two m-adic
  logarithms and applications to Diophantine problems*, Compositio Math. 132 (2002), 137-158 (p. 139), in the case
  $g = 1$, for a general modulus $m$; the theorems of revision r7 take `hB1 : Thm1G1 8` as an argument, so what is
  proved is the implication `Thm1G1 8 → …`. `#print axioms` lists axioms only, not hypotheses, so `Thm1G1` does not
  appear in its output. It is used in exactly one place, `Collatz.M1.hgt_thm1` (`CollatzProof/M1/S13B.lean`,
  Proposition 15.5 of the paper: the height condition for window widths $c_D \le 9 \times 10^{-3}$), through
  `J1_bug`. The header of `Thm1Defs.lean` lists the correspondence with the original item by item; Appendix B.1 of
  the paper reproduces the statement and gives the correspondence as a proposition. If the transcription were false,
  the theorems of revision r7 would be vacuous, so it should be compared with the original paper.
  - *The reading of condition (1).* The original prints the last two terms of condition (1) as
    $\gamma_1 L R \max\lbrace \left|x_1\right|, \left|y_1\right| \rbrace$ and
    $\gamma_2 L S \max\lbrace \left|x_2\right|, \left|y_2\right| \rbrace$, without a logarithm. The transcription
    reads them as logarithmic heights $\log \max\lbrace \left|x_i\right|, \left|y_i\right| \rbrace$ (`logHt`),
    correcting what we take to be a misprint; the reasons are given in Section 15.4 of the paper and in the header of
    `Thm1Defs.lean`. With this reading condition (1) is easier to satisfy than with the literal print, so the
    transcribed theorem is stronger than the literal print.
  - *Two premises that only weaken the statement.* `Thm1G1` asserts the conclusion only when
    $\Lambda = (x_1/y_1)^{b_1} - (x_2/y_2)^{b_2} \ne 0$ (the original defines $v_m$ only for nonzero numbers) and
    $x_2/y_2 \ne 1$ (the premise `r₂ ≠ 1` of `Prem`, so that nothing depends on the convention $v_p(0) = +\infty$;
    Proposition 15.5 treats the case $x_2/y_2 = 1$ separately, without Theorem 1). The other choices (nonzero
    integers $x_i$, $y_i$ not necessarily in lowest terms, with the heights of the given representation; the
    convention of `VpGe`; the cardinality conditions in natural numbers) are equivalent to the original.
  - *Checks.* The transcription was compared with the primary source in an independent review, which found it no
    stronger than the printed theorem under the reading of condition (1) with logarithmic heights, and which also
    searched numerically for counterexamples (about $4.8 \times 10^5$ instances; none found).
    `Collatz.M1.thm1G1_eight_premises_satisfiable` proves that the premises of `Thm1G1 8` (`Prem`, condition (1) and
    $\Lambda \ne 0$) can be satisfied simultaneously, so the hypothesis is not vacuously true.
    `Collatz.M1.Bugeaud.thm1G1_iff_red` proves that `Thm1G1 m` is equivalent to the form `Thm1G1Red m` stated with
    the heights of the fractions in lowest terms.
- **`BugeaudHyp` (the route of revision r6).** `Collatz.M1.BugeaudHyp` (`CollatzProof/M1/DeepDefs.lean`) states
  Theorem 2 of Bugeaud (2002) in the case $m = 8$, $\mu = 4$, multiplicatively independent rationals,
  $c_2(4) = 53.6$, with the narrower side condition "$b_2$ odd". The statements of revision r6 and their explicit
  values take `hBug : BugeaudHyp` as an argument; it is used only in `Collatz.M1.hgt` (`CollatzProof/M1/S13.lean`,
  Proposition 15.3 of the paper). `CollatzProof/M1/BugeaudBridge.lean` states Theorem 2 of Bugeaud (2002) for
  general $m$ and $\mu$, as a transcription of the original (`Collatz.M1.Bugeaud.Thm2`), and proves in the kernel
  `bugeaudHyp_of_thm2 : Thm2 8 4 → BugeaudHyp`, through `bugeaudHyp_of_thm2C2Narrow`, whose premise has the extra
  condition `p ∤ b₂` of Bugeaud's Theorem 1 (which the proof of his Theorem 2 uses), so the bridge holds under either
  reading. Theorem 2 does not involve the reading of condition (1) above. Appendix B.2 of the paper gives the
  correspondence with the original item by item.
- **`RhinHyp` is proved.** `sigma_v3`, `sigma_main` and the other stopping-time statements in `CollatzProof` also
  assume the Rhin-type bound `RhinHyp` ($\lVert q \log_2 3 \rVert \ge C q^{-\kappa}$ for all $q \ge 1$).
  `CollatzND.rhinHyp_holds` proves it from `Erdos1135.ND.existsPhaseGapRhin` of Mazur's formalization
  ($\kappa = 13.3$), and the statements in `CollatzND` are the resulting ones, with `Thm1G1 8` (respectively
  `BugeaudHyp`) as the only hypothesis.

The hypotheses as printed by `#print` in `verify/Probe.lean`:

```lean
def Collatz.M1.Bugeaud.Thm1G1 : ℕ → Prop :=
fun m =>
  ∀ (x₁ y₁ x₂ y₂ : ℤ) (b₁ b₂ K L R₁ R₂ S₁ S₂ : ℕ),
    x₁ ≠ 0 →
      y₁ ≠ 0 →
        x₂ ≠ 0 →
          y₂ ≠ 0 →
            Collatz.M1.Bugeaud.Prem m (↑x₁ / ↑y₁) (↑x₂ / ↑y₂) b₁ b₂ K L R₁ R₂ S₁ S₂ →
              0 <
                  Collatz.M1.Bugeaud.cond1 m (Collatz.M1.Bugeaud.logHt x₁ y₁) (Collatz.M1.Bugeaud.logHt x₂ y₂) b₁ b₂ K L
                    R₁ R₂ S₁ S₂ →
                (↑x₁ / ↑y₁) ^ b₁ - (↑x₂ / ↑y₂) ^ b₂ ≠ 0 →
                  ↑(Collatz.M1.Bugeaud.vm m ((↑x₁ / ↑y₁) ^ b₁ - (↑x₂ / ↑y₂) ^ b₂)) <
                    ↑K * ↑L + ↑(Collatz.M1.Bugeaud.hMax m b₁ b₂) - 1 / 2
def Collatz.M1.Bugeaud.Prem : ℕ → ℚ → ℚ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop :=
fun m r₁ r₂ b₁ b₂ K L R₁ R₂ S₁ S₂ =>
  1 < m ∧
    r₁ ≠ 0 ∧
      r₂ ≠ 0 ∧
        r₁ ≠ 1 ∧
          r₁ ≠ -1 ∧
            r₂ ≠ 1 ∧
              0 < b₁ ∧
                0 < b₂ ∧
                  (∀ p ∈ m.primeFactors, padicValRat p r₁ = 0 ∧ padicValRat p r₂ = 0) ∧
                    Collatz.M1.Bugeaud.H1 m 1 r₁ r₂ ∧
                      Collatz.M1.Bugeaud.H2 m 1 r₁ r₂ ∧
                        3 ≤ K ∧
                          2 ≤ L ∧
                            0 < R₁ ∧
                              0 < R₂ ∧
                                0 < S₁ ∧
                                  0 < S₂ ∧
                                    (∀ p ∈ m.primeFactors, ¬p ∣ b₂ / p ^ Collatz.M1.Bugeaud.hExp p b₁ b₂) ∧
                                      L ≤ (Collatz.M1.Bugeaud.set1 r₁ r₂ R₁ S₁).card ∧
                                        (K - 1) * L < (Collatz.M1.Bugeaud.set2 b₁ b₂ R₂ S₂).card
def Collatz.M1.Bugeaud.cond1 : ℕ → ℝ → ℝ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ :=
fun m H₁ H₂ b₁ b₂ K L R₁ R₂ S₁ S₂ =>
  ↑K * (↑L - 1) * Real.log ↑m - (1 + 2 * ↑m.primeFactors.card) * Real.log ↑(K * L) -
        (↑K - 1) * Real.log (Collatz.M1.Bugeaud.bB K (R₁ + R₂ - 1) (S₁ + S₂ - 1) b₁ b₂) -
      Collatz.M1.Bugeaud.gam1 1 ↑(R₁ + R₂ - 1) ↑(S₁ + S₂ - 1) ↑(K * L) * ↑L * ↑(R₁ + R₂ - 1) * H₁ -
    Collatz.M1.Bugeaud.gam2 1 ↑(R₁ + R₂ - 1) ↑(S₁ + S₂ - 1) ↑(K * L) * ↑L * ↑(S₁ + S₂ - 1) * H₂
def Collatz.M1.Bugeaud.logHt : ℤ → ℤ → ℝ :=
fun x y => Real.log (max |↑x| |↑y|)
def Collatz.M1.Bugeaud.bB : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ :=
fun K R S b₁ b₂ => ((↑R - 1) * ↑b₂ + (↑S - 1) * ↑b₁) / 2 * Collatz.M1.Bugeaud.factProd K ^ (-2 / (↑K ^ 2 - ↑K))
def Collatz.M1.Bugeaud.factProd : ℕ → ℝ :=
fun K => ∏ k ∈ Finset.Icc 1 (K - 1), ↑k.factorial
def Collatz.M1.Bugeaud.gam1 : ℝ → ℝ → ℝ → ℝ → ℝ :=
fun g R S N => (R + g - 1) / (2 * R) - g * N / (6 * R * (S + g - 1))
def Collatz.M1.Bugeaud.gam2 : ℝ → ℝ → ℝ → ℝ → ℝ :=
fun g R S N => (S + g - 1) / (2 * S) - g * N / (6 * S * (R + g - 1))
def Collatz.M1.Bugeaud.hExp : ℕ → ℕ → ℕ → ℕ :=
fun p b₁ b₂ => padicValNat p (b₁.gcd b₂)
def Collatz.M1.Bugeaud.hMax : ℕ → ℕ → ℕ → ℕ :=
fun m b₁ b₂ => m.primeFactors.sup fun p => Collatz.M1.Bugeaud.hExp p b₁ b₂
def Collatz.M1.Bugeaud.set1 : ℚ → ℚ → ℕ → ℕ → Finset ℚ :=
fun r₁ r₂ R₁ S₁ => Finset.image (fun rs => r₁ ^ rs.1 * r₂ ^ rs.2) (Finset.range R₁ ×ˢ Finset.range S₁)
def Collatz.M1.Bugeaud.set2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ :=
fun b₁ b₂ R₂ S₂ => Finset.image (fun rs => rs.1 * b₂ + rs.2 * b₁) (Finset.range R₂ ×ˢ Finset.range S₂)
def Collatz.M1.Bugeaud.H1 : ℕ → ℕ → ℚ → ℚ → Prop :=
fun m g r₁ r₂ =>
  ∀ p ∈ m.primeFactors,
    Collatz.M1.Bugeaud.VpGe p (r₁ ^ g - 1) ↑(m.factorization p) ∧ Collatz.M1.Bugeaud.VpGe p (r₂ ^ g - 1) 1
def Collatz.M1.Bugeaud.H2 : ℕ → ℕ → ℚ → ℚ → Prop :=
fun m g r₁ r₂ => 2 ∣ m → Collatz.M1.Bugeaud.VpGe 2 (r₁ ^ g - 1) 2 ∧ Collatz.M1.Bugeaud.VpGe 2 (r₂ ^ g - 1) 2
def Collatz.M1.Bugeaud.VpGe : ℕ → ℚ → ℤ → Prop :=
fun p z k => z = 0 ∨ k ≤ padicValRat p z
def Collatz.M1.Bugeaud.vm : ℕ → ℚ → ℤ :=
fun m x => ↑(Collatz.M1.Bugeaud.vmNat m x.num.natAbs) - ↑(Collatz.M1.Bugeaud.vmNat m x.den)
def Collatz.M1.Bugeaud.vmNat : ℕ → ℕ → ℕ :=
fun m n => Nat.findGreatest (fun v => m ^ v ∣ n) n
def Collatz.M1.BugeaudHyp : Prop :=
∀ (r₁ r₂ : ℚ) (g b₁ b₂ : ℕ) (A₁ A₂ : ℝ),
  r₁ ≠ 0 →
    r₂ ≠ 0 →
      r₁ ≠ 1 →
        r₁ ≠ -1 →
          Collatz.M1.v2q r₁ = 0 →
            Collatz.M1.v2q r₂ = 0 →
              1 ≤ g →
                g % 2 = 1 →
                  3 ≤ Collatz.M1.v2q (r₁ ^ g - 1) →
                    2 ≤ Collatz.M1.v2q (r₂ ^ g - 1) →
                      1 ≤ b₁ →
                        1 ≤ b₂ →
                          b₂ % 2 = 1 →
                            Collatz.M1.MulIndep r₁ r₂ →
                              1 < A₁ →
                                1 < A₂ →
                                  Real.log |↑r₁.num| ≤ Real.log A₁ →
                                    Real.log ↑r₁.den ≤ Real.log A₁ →
                                      Real.log 8 ≤ Real.log A₁ →
                                        Real.log |↑r₂.num| ≤ Real.log A₂ →
                                          Real.log ↑r₂.den ≤ Real.log A₂ →
                                            Real.log 8 ≤ Real.log A₂ →
                                              ↑(Collatz.M1.v8 (r₁ ^ b₁ - r₂ ^ b₂)) ≤
                                                53.6 * ↑g / Real.log 8 ^ 4 *
                                                      max
                                                          (Real.log (↑b₁ / Real.log A₂ + ↑b₂ / Real.log A₁) +
                                                              Real.log (Real.log 8) +
                                                            0.64)
                                                          (4 * Real.log 8) ^
                                                        2 *
                                                    Real.log A₁ *
                                                  Real.log A₂
def Collatz.M1.v8 : ℚ → ℤ :=
fun x => ↑(padicValInt 2 x.num / 3) - ↑(padicValNat 2 x.den / 3)
def Collatz.M1.v2q : ℚ → ℤ :=
fun x => padicValRat 2 x
def Collatz.M1.MulIndep : ℚ → ℚ → Prop :=
fun r₁ r₂ => ∀ (k₁ k₂ : ℤ), r₁ ^ k₁ * r₂ ^ k₂ = 1 → k₁ = 0 ∧ k₂ = 0
def Collatz.M1.RhinHyp : Prop :=
∃ C κ, 0 < C ∧ ∀ (q : ℕ), 0 < q → C * ↑q ^ (-κ) ≤ |↑q * Collatz.M1.lam - ↑(round (↑q * Collatz.M1.lam))|
```

### Axioms

`#print axioms` for each of the nineteen declarations named in `verify/Probe.lean` (the eight theorems of
revision r7 and the six of revision r6 displayed above, `Collatz.M1.hgt_thm1`,
`Collatz.M1.thm1G1_eight_premises_satisfiable`, `Collatz.M1.Bugeaud.thm1G1_iff_red`,
`Collatz.M1.Bugeaud.bugeaudHyp_of_thm2` and `CollatzND.rhinHyp_holds`) reports only

```
[propext, Classical.choice, Quot.sound]
```

There is no `sorry`, no `axiom` declaration, and no `native_decide`, `#eval`, `run_cmd` or `implemented_by` in the
sources of this repository. `lake build` prints one `declaration uses 'sorry'` warning, for
`vendor/mazur/FormalConjectures/Wikipedia/CollatzConjecture.lean` of Mazur's formalization (the statement of the
Collatz conjecture itself); the theorems above do not depend on it, as `#print axioms` shows (no `sorryAx`).

### Specification tests

The inequalities above are asymptotic and cannot be tested on small values. `CollatzProof/M1/Spec.lean` (part of
the default `lake build`, about 10 seconds; not used by any proof) instead checks that the definitions in the
statements mean what the paper says (the definition of $\mathcal{N}_K$ and the remark comparing the coefficient
stopping time with the stopping time, in Section 3 of the paper, "Notation and setting of the problem"):

- **Survival is an integer condition** (proved): `spec_survW_iff : SurvW 0 (pw n K) ↔ ∀ j, 1 ≤ j → j ≤ K →
  2 ^ j ≤ 3 ^ ones (pw n K) j`, i.e. the real height condition $\lambda o_j - j \ge 0$ is
  $3^{o_j}/2^j \ge 1$ (coefficient stopping time $> K$); `spec_ones_pw`: for $j \le K$, `ones (pw n K) j` is the
  number of odd terms among $n, T(n), \ldots, T^{j-1}(n)$.
- **Counts** (proved reductions plus `decide`): `spec_NKcount_eq` and `spec_SigmaCount_eq` rewrite `NKcount` and
  `SigmaCount` as decidable counts. For $(K, X) = (5, 40), (8, 100), (10, 200), (12, 300)$, `NKcount K X` is
  5, 6, 13, 19 and `SigmaCount K X` is 6, 7, 14, 20 (the difference is $n = 1$); `NKcount 0 10 = 10`;
  $\mathcal{N}_5 \cap [1, 40] = \lbrace 7, 15, 27, 31, 39 \rbrace$ and
  $\lbrace 1 \le n \le 40 : \sigma(n) > 5 \rbrace = \lbrace 1, 7, 15, 27, 31, 39 \rbrace$. The same values were
  computed by an independent brute force in Python (`audit/m1_spec.py` in the source repository, not included
  here).
- **`DivCount`**: `spec_one_le_DivCount` (`1 ≤ DivCount X` for `X ≥ 1`, from $n = 1$) and
  `spec_DivCount_100 : DivCount 100 = 1`.
- **Individual values**: `T 27 = 41`, `pw 27 5 = ![true, true, false, true, true]`, $1 \in \mathcal{N}_1$ and
  $1 \notin \mathcal{N}_2$, the coefficient stopping time and the stopping time of 27 are both 59;
  `spec_mem_Icc_floor`: `n ∈ Icc 1 ⌊x⌋₊ ↔ 1 ≤ n ∧ n ≤ x` for `x ≥ 0` (the reading of `⌊2 ^ (α * K)⌋₊`).

Only `decide` and `rfl` are used for the computations, so every value is checked by the kernel. `#print axioms` for
the theorems of `Spec.lean` reports `[propext, Classical.choice, Quot.sound]` or fewer.

### What rests on the written proof or on reading

- **The transcriptions of Bugeaud's theorems.** Whether `Thm1G1` says what the printed Theorem 1 of Bugeaud (2002)
  says, under the reading of condition (1) with logarithmic heights, and whether `Thm2` (and hence `BugeaudHyp`)
  says what the printed Theorem 2 says, is a matter of reading, not of the kernel. Both transcriptions were compared
  with the primary source in independent reviews. The reading of condition (1) makes Theorem 1 stronger than its
  literal print; the qualitative statements are also proved under `BugeaudHyp`, which does not involve this reading.
- **The meaning of the statements.** The main statements and the definitions occurring in them (printed above) are
  short enough to be read directly; the specification tests check them on small values.
- **The remaining explicit constants.** The values $\varepsilon(0.6) = 2.46 \times 10^{-11}$ and
  $1 - c - 5.84 \times 10^{-11}$ (and those of revision r6, $5.35 \times 10^{-14}$ and $1.33 \times 10^{-13}$) are
  formalized, with a fixed $\delta$ that covers $\alpha \in [0.5114, 0.659]$. The values of $\varepsilon(\alpha)$ for
  $\alpha < 0.5114$ in the table of Section 16.3 of the paper and the thresholds of Section 16.4 rest on the written
  proof. `verify/proof_pf_certified_v3.py` certifies the 246 numerical claims of the written proof (constants of
  revision r7) with rigorous interval arithmetic in exact rational numbers; `verify/proof_pf_certified.py`, the
  interval library it imports, also certifies the 195 claims of revision r6. The certifying programs themselves have
  not been verified.
- **The extension to the maps $3x + d$** (Section 18 of the paper) is not formalized.

### Review status

The work has not yet been reviewed by independent human experts; no human mathematician has reviewed the proofs.
Formal verification does not replace independent review of the exposition or of the correspondence between the
informal and formal statements.

## Repository layout

| Path | Content |
|---|---|
| `CollatzProof/Core/Defs.lean`, `CollatzProof/Defs.lean` | The shortcut map `T` (in `Core/Defs.lean`, shared with another development of the source repository), the number of odd steps `o`, the additive term `c`, the dual Terras identity $2^j T^j(n) = 3^{o_j} n + c_j$. |
| `CollatzProof/Fiber.lean` | Terras injectivity (parity words of length $t$ determine $n < 2^t$) and fiber bounds. |
| `CollatzProof/M1/Defs.lean`, `Basics.lean`, `Counting.lean` | Notation of Section 3 of the paper (words, heights, survival, slices; $R_\delta$ with its constants as parameters, `RdeltaG`), common results of Sections 3-4, counting. |
| `CollatzProof/M1/S4.lean` ... `S14.lean` | One file per section: `S4` Theorem A and Corollary A (Section 6 of the paper; general forms `C_thmAG`, `C_corAG`), `S5` Theorem B (Section 7; `thmBG`), `S6` counting swap blocks (Section 8), `S7` shallow frequencies (Section 9), `S9` outer shells (Section 11), `S10` Hölder reduction (Section 12), `S11` physical side and Bhattacharyya coefficients (Sections 13-14), `S13` the height condition (HGT) from Theorem 2 of Bugeaud (Section 15; the only use of `BugeaudHyp`), `S14` assembly and `m1_main` (Section 16; general forms `HgtSupply`, `K_coreG`, `all_shellsG`, `m1_mainG`). The tools for the phases (Section 10) are in `Phase.lean`. |
| `CollatzProof/M1/Thm1Defs.lean` | The transcription `Bugeaud.Thm1G1 m` of Theorem 1 of Bugeaud (2002) (case $g = 1$, general $m$), its notation, the correspondence with the original, and `thm1G1_iff_red`. |
| `CollatzProof/M1/Thm1Anal.lean`, `S13B.lean` | Proposition 15.5 of the paper (`hgt_thm1`: the height condition for $c_D \le 9 \times 10^{-3}$ from `Thm1G1 8`; the only use of `Thm1G1`), the check of condition (1) (`T1_cond1`), the application `J1_bug`, and `thm1G1_eight_premises_satisfiable`. |
| `CollatzProof/M1/ThmAV3.lean` | Theorem A and Corollary A with the constants of revision r7 (`thmA_v3`, `corA_v3`). |
| `CollatzProof/M1/ExplicitNumV3.lean`, `ExplicitV3.lean` | The explicit values of revision r7: the numerical lemmas for $p = 247$, Proposition 16.2 with the constants of Section 16.1 (`K_core_v3`, `all_shells_v3`), `m1_v3`, `m1_v3_06`, `sigma_v3`, `sigma_v3_06`, `divergent_count_v3`, and the qualitative `m1_main_thm1`, `sigma_main_thm1`, `divergent_count_thm1` (via `hgt_supply_thm1`). |
| `CollatzProof/M1/ExplicitNum.lean`, `ExplicitCore.lean`, `Explicit.lean` | The explicit values of revision r6 under `BugeaudHyp` (`m1_explicit_06`, `sigma_explicit_06`, `divergent_count_explicit`), and the general form `K_core_paramG` of Proposition 16.2 with the constants as hypotheses. |
| `CollatzProof/M1/Sigma.lean` | Section 17: transfer to the stopping time $\sigma$ (`sigma_main`, `divergent_count`, under `RhinHyp`; general forms `sigma_mainG`, `divergent_countG`). |
| `CollatzProof/M1/Spec.lean` | Specification tests for the definitions in the statements (see "Specification tests"); not used by any proof. |
| `CollatzProof/M1/{Fourier,ShellDefs,DeepDefs}.lean` | Definitions: Fourier transform and condition (WF) (`WFG`, `WF`); swap blocks, shells, depth; deep frequencies, lattice condition, `BugeaudHyp`. |
| `CollatzProof/M1/BugeaudBridge.lean` | Theorem 2 of Bugeaud (2002) stated for general $m$ and $\mu$ as in the original (`Collatz.M1.Bugeaud.Thm2`), and the kernel-checked bridge `bugeaudHyp_of_thm2 : Thm2 8 4 → BugeaudHyp`, which goes through `bugeaudHyp_of_thm2C2Narrow` (premise with the extra condition `p ∤ b₂` of Bugeaud's Theorem 1, which the proof of his Theorem 2 uses), so the bridge holds under either reading. It also defines the valuations `vmNat`, `vm` and `VpGe` used by `Thm1G1`. |
| `CollatzProof/M1/{C,D,E,G,I,K}_*.lean` | Auxiliary lemmas, grouped by the work package named by the prefix (C: Sections 4-6, D: Theorem B of Section 7, E: Section 8, G: Sections 10-11, I: Sections 13-14, K: Section 16; the `J_` lemmas of Section 15 are in `S13.lean`, the `J1_` and `T1_` lemmas of Section 15.4 in `S13B.lean` and `Thm1Anal.lean`). |
| `CollatzProof/M1/Compat.lean` | Replacements for lemmas whose names differ between Lean/Mathlib v4.30.0-rc2 and v4.34.1 (the same sources build with both). |
| `CollatzND/Rhin.lean` | Mazur's Rhin-type phase gap rewritten in the form of `RhinHyp`. |
| `CollatzND/M1Sigma.lean` | `rhinHyp_holds`, `m1_sigma`, `m1_divergent` (only `BugeaudHyp` remains). |
| `CollatzND/M1Explicit.lean` | `m1_sigma_explicit_06`, `m1_sigma_explicit`, `m1_divergent_explicit` (explicit values of revision r6; only `BugeaudHyp` remains). |
| `CollatzND/M1ExplicitV3.lean` | `m1_sigma_thm1`, `m1_sigma_v3`, `m1_sigma_v3_06`, `m1_divergent_thm1`, `m1_divergent_v3` (only `Thm1G1 8` remains). |
| `verify/Probe.lean` | Prints the statements, the definitions used in them, the hypotheses, and the axioms (not part of any library). |
| `verify/proof_pf_certified_v3.py` | Certifies, with rigorous interval arithmetic in exact rational numbers (Python standard library, about 15 s), the 246 numerical claims of the written proof with the constants of revision r7 (e.g. $\varepsilon(0.6) \ge 2.46 \times 10^{-11}$, the thresholds of Section 16.4, and condition (1) of Bugeaud's Theorem 1 in the application of Section 15.4). Run `python3 verify/proof_pf_certified_v3.py`; it prints one line per claim and a summary, and exits with code 1 if any claim fails. |
| `verify/proof_pf_certified.py` | The interval library imported by `proof_pf_certified_v3.py` (keep both files in the same directory); run on its own, it certifies the 195 numerical claims of revision r6 (about 13 s). |
| `verify/*.log` | Verification records (see "Verification records"). |
| `fetch_mazur.py` | Downloads Mazur's formalization and checks SHA-256 hashes. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake project (Lean v4.30.0-rc2, Mathlib v4.30.0-rc2). |
| `MANIFEST.sha256` | SHA-256 of every file in this repository except itself. |
| `README.md`, `LICENSE`, `NOTICE` | This file; the Apache License, Version 2.0; the copyright and third-party notice. |

Section numbers in the file names (`S4` ... `S14`) and in the comments of the Lean sources follow an earlier
numbering of the proof (the Japanese proof manuscript): section §k there is Section k+2 of the paper, and §14.5 there
is Section 17. The numbers of individual statements in the comments follow the same earlier numbering and may differ
from those of the paper; Appendix C of the paper gives the correspondence. The comments on the parts added for
revision r7 cite version 3 of that manuscript: §4.2 there is Section 6 of the paper (Theorem A), §13.5 is
Section 15.4 (Proposition 13.2B there is Proposition 15.5), §14.6 is Sections 16.1 and 16.3, and Lemma 14.0 is
Lemma 16.1; where it matters, the comments also give the number in the paper.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain in `lean-toolchain`, Lean v4.30.0-rc2, is
installed automatically), `git`, Python 3 (standard library only). In the root directory of a clone of this
repository:

```sh
sha256sum -c MANIFEST.sha256    # optional: compare every file with its SHA-256 in the manifest
python3 fetch_mazur.py          # Mazur's formalization -> vendor/mazur   (ZIP and per-file SHA-256 checked)
lake exe cache get              # Mathlib v4.30.0-rc2 cache
lake build                      # builds CollatzProof and CollatzND (and the needed part of Mazur's formalization)
lake env lean verify/Probe.lean                          # statements, definitions, hypotheses and axioms
lake env leanchecker --fresh CollatzND.M1ExplicitV3      # re-check every declaration incl. Mathlib in the kernel (about 35 minutes)
lake env leanchecker --fresh CollatzND.M1Explicit        # the same for the statements of revision r6 (about 35 minutes)
python3 verify/proof_pf_certified_v3.py                  # certify the numerical claims of the written proof (about 15 s; not Lean)
```

`lake build` also builds `CollatzProof/M1/Spec.lean` (the specification tests). The dependency closure of
`CollatzND.M1ExplicitV3` contains all the theorems displayed above except those of `CollatzND/M1Explicit.lean`,
together with `BugeaudBridge.lean` and `CollatzND/M1Sigma.lean`; that of `CollatzND.M1Explicit` contains the
statements of revision r6. Mazur's formalization is not redistributed here; `fetch_mazur.py` downloads it from its
original location and verifies it by hash: L. Mazur, *Natural-density Collatz descent in logarithmic time*, Lean
formalization hosted by ProofAtlas, commit `ca3dd0d63920411213403092aecc6946619eb082`, ZIP SHA-256
`5761e6bdad1284275f3a19aa51d8278a68b19cb569c516c20df956e6fac91864` (Apache-2.0). Only the import closure of
`Erdos1135.ND.RhinPhaseGap` is used.

## Versions

Lean v4.30.0-rc2 (`lean-toolchain`) and Mathlib tag v4.30.0-rc2 (pinned by `lake-manifest.json`). This release
candidate is the version of Mazur's formalization, which is needed to prove `RhinHyp`; with the same toolchain the
stopping-time statements have `Thm1G1 8` (respectively `BugeaudHyp`) as their only hypothesis. The files under
`CollatzProof/` also build with Lean v4.34.1 and Mathlib v4.34.1 in the source repository (that build states the
stopping-time results with `RhinHyp` as a hypothesis); `CollatzProof/M1/Compat.lean` replaces the lemmas whose names
differ between the two versions.

## Verification records

The logs in `verify/` were produced on 2026-09-28 in a fresh copy of the files of this repository (the Lean sources,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `fetch_mazur.py` and `verify/Probe.lean` identical to those
listed in `MANIFEST.sha256`), with Mazur's formalization downloaded by `fetch_mazur.py` and the Mathlib packages
fetched by `lake exe cache get`. `leanchecker --fresh` re-checks every declaration of the dependency closure,
including Mathlib, in the kernel; it prints nothing on success. In the logs, the absolute path of the working copy
is replaced by `<copy>`.

| Log | Content |
|---|---|
| `lake-build-2026-09-28.log` | `python3 fetch_mazur.py`, `lake exe cache get` and `lake build` (exit code 0, 8413 jobs, about 7 minutes including the downloads). |
| `probe-2026-09-28.log` | Output of `lake env lean verify/Probe.lean`: statements, axioms (only `[propext, Classical.choice, Quot.sound]`), hypotheses and definitions. |
| `leanchecker-fresh-M1ExplicitV3-2026-09-28.log` | `lake env leanchecker --fresh CollatzND.M1ExplicitV3` (exit code 0, 33 minutes; the last line names the module and the exit code). |
| `leanchecker-fresh-M1Explicit-2026-09-28.log` | `lake env leanchecker --fresh CollatzND.M1Explicit` (exit code 0, 33 minutes; run in parallel with the previous one). |
| `manifest-check-2026-09-29.log` | `sha256sum -c MANIFEST.sha256` in a second fresh copy of this repository, made after the logs above were added; the manifest checked there does not list this log, which was added afterwards (a file cannot contain its own hash). |

## License

The Lean code and scripts in this repository are licensed under the Apache License, Version 2.0 (see `LICENSE`).
See `NOTICE` for the copyright and the third-party notice.

| Component | Use in this repository | Copyright | License |
|---|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4), tag v4.30.0-rc2, with the Lean packages it requires (pinned in `lake-manifest.json`) | Dependency, fetched at build time by Lake; not included | The Mathlib authors (named in each file) | Apache-2.0 (Mathlib); the other packages under their own licenses |
| L. Mazur, *Natural-density Collatz descent in logarithmic time*, Lean formalization hosted by ProofAtlas, commit `ca3dd0d63920411213403092aecc6946619eb082` | Dependency, fetched at build time by `fetch_mazur.py` into `vendor/mazur`; not included | Copyright 2026 Advameg, Inc. | Apache-2.0 |

No file in this repository is derived from third-party code: no third-party files are included, and no patch is
applied. `CollatzND/Rhin.lean` imports the theorem `Erdos1135.ND.existsPhaseGapRhin` of Mazur's formalization and
uses it unchanged. Mazur's formalization, including the Formal Conjectures material it retains, stays under its own
`LICENSE` and `NOTICE`, which `fetch_mazur.py` unpacks with the sources into `vendor/mazur`.

The paper itself is not part of this repository; it is distributed on Zenodo
([doi:10.5281/zenodo.22986641](https://doi.org/10.5281/zenodo.22986641)) under the license stated there.

## How to cite

```bibtex
@misc{nashida2026terras,
  author    = {Hiroyuki Nashida},
  title     = {A strict improvement of the Terras-type bound for integers with long Collatz stopping times},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22986641},
  url       = {https://doi.org/10.5281/zenodo.22986641},
  note      = {Preprint}
}
```

## Attribution and the role of AI

- No file in this repository is derived from third-party code. The Rhin-type phase gap
  `Erdos1135.ND.existsPhaseGapRhin` is a theorem of Mazur's formalization, used unchanged.
- Bugeaud's theorems are not formalized. Theorem 1 of Bugeaud (2002) enters only as the hypothesis `Thm1G1 8`
  (`Thm1Defs.lean` transcribes its statement for $g = 1$), and Theorem 2 only as the hypothesis `BugeaudHyp`
  (`BugeaudBridge.lean` transcribes its statement); neither is proved here.
- All code of this project (the Lean sources in `CollatzProof/` and `CollatzND/`, `verify/Probe.lean`, and the
  Python scripts) was written with Anthropic's Claude models through Claude Code, directed by the author. The Lean
  proofs are checked by the Lean kernel, and this check does not depend on how the code was produced. No human
  mathematician has reviewed the proofs.
- The comments were translated from Japanese. The code is identical to the checked originals: a script in the
  source repository (`check_lean_bundle.py`, in the directory of the paper) confirms that, after removing comments,
  every Lean file except `verify/Probe.lean` (which exists only here) is byte-for-byte identical to its original.
