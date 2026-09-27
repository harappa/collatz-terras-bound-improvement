# A strict improvement of the Terras-type bound for integers with long Collatz stopping times

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22986641.svg)](https://doi.org/10.5281/zenodo.22986641)

This repository contains the Lean 4 formalization accompanying the preprint *A strict improvement of the
Terras-type bound for integers with long Collatz stopping times* by Hiroyuki Nashida (Zenodo, 2026,
doi:[10.5281/zenodo.22986641](https://doi.org/10.5281/zenodo.22986641)). It formalizes, with Mathlib, the
qualitative form of the main theorem of the paper (for every $\alpha \in (1/2, 0.659]$ some $\varepsilon > 0$
lowers the Terras-type exponent $\alpha(1-c)$ for integers with coefficient stopping time larger than $K$), its
version for the stopping time, and the corollary on integers whose orbit never drops below the starting value,
with Theorem 2 of Bugeaud (2002) as an explicit hypothesis; the explicit value of $\varepsilon$ in the paper is
not formalized.

## Paper

- **Author:** Hiroyuki Nashida
- **Title:** A strict improvement of the Terras-type bound for integers with long Collatz stopping times
- **Preprint:** Zenodo, 2026
- **DOI:** [10.5281/zenodo.22986641](https://doi.org/10.5281/zenodo.22986641)
- **Lean formalization:** this repository

Revision r6 (September 27, 2026). This repository accompanies revision r6 of the paper; the revision number is
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
Theorem 2, with $m = 8$).

*What is verified and how.* The qualitative statements (existence of some $\varepsilon > 0$) are formalized in
Lean 4; the special case of Bugeaud's theorem enters the formalization as an explicit hypothesis; its derivation
from a Lean transcription of the published theorem is machine-checked, the transcription itself was compared with
the primary source, and apart from this hypothesis only the three axioms used throughout Mathlib appear. The
explicit value $\varepsilon(0.6) = 5.35 \times 10^{-14}$ comes from the written proof; all numerical inequalities
behind it (195 of them) have been checked with rigorous interval arithmetic in exact rational numbers, but not in
Lean. The Lean code is available in this repository.

## Main results in Lean

The formalized statements are the qualitative forms (existence of some $\varepsilon > 0$) of Theorem 1.1,
Theorem 1.2 and Corollary 1.3 of the paper. Output of `#check` in `verify/Probe.lean`:

```lean
Collatz.M1.m1_main (hBug : Collatz.M1.BugeaudHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
  ∃ ε > 0, ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.NKcount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
CollatzND.m1_sigma (hBug : Collatz.M1.BugeaudHyp) (α : ℝ) (hα : 1 / 2 < α) (hα' : α ≤ 0.659) :
  ∃ ε > 0, ∃ K0, ∀ K ≥ K0, ↑(Collatz.M1.SigmaCount K ⌊2 ^ (α * ↑K)⌋₊) ≤ 2 ^ ((α * (1 - Collatz.M1.cc) - ε) * ↑K)
CollatzND.m1_divergent (hBug : Collatz.M1.BugeaudHyp) :
  ∃ ε > 0, ∃ x0, ∀ x ≥ x0, ↑(Collatz.M1.DivCount x) ≤ ↑x ^ (1 - Collatz.M1.cc - ε)
```

The definitions occurring in these statements, as printed by `#print` in `verify/Probe.lean`:

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
```

In words, with $T$ the shortcut map, $o_j(n)$ the number of odd terms among $n, T(n), \ldots, T^{j-1}(n)$, and
$c = 1 - H(1/\log_2 3) \approx 0.050044$ ($H$ the binary entropy in bits):

- **`m1_main`** (Theorem 1.1, qualitative form). For every $\alpha \in (1/2, 0.659]$ there are $\varepsilon > 0$
  and $K_0$ such that for all $K \ge K_0$ the number of $1 \le n \le 2^{\alpha K}$ with $3^{o_j(n)} \ge 2^j$ for
  all $1 \le j \le K$ (coefficient stopping time $> K$) is at most $2^{(\alpha(1-c) - \varepsilon)K}$. The
  Terras-type count gives the exponent $\alpha(1-c)$.
- **`m1_sigma`** (Theorem 1.2, qualitative form). The same bound for the number of $1 \le n \le 2^{\alpha K}$ with
  $T^j(n) \ge n$ for all $1 \le j \le K$ (stopping time $\sigma(n) > K$).
- **`m1_divergent`** (Corollary 1.3, qualitative form). There are $\varepsilon > 0$ and $x_0$ such that for all
  $x \ge x_0$ the number of $1 \le n \le x$ with $\sigma(n) = \infty$ (that is, $T^j(n) \ge n$ for every
  $j \ge 1$) is at most $x^{1-c-\varepsilon}$. ($n = 1$ is counted, since $T(1) = 2$ and $T(2) = 1$.)

The namespace `Collatz.M1` is named after an internal label of the project; it has no mathematical meaning. The
same label occurs in the directory `CollatzProof/M1/`, in the file `CollatzND/M1Sigma.lean` and in the theorem
names `m1_main`, `m1_sigma` and `m1_divergent`.

## What is and is not verified

The Lean kernel certifies that the statements above follow from the hypothesis `BugeaudHyp` within Mathlib, using
no axioms beyond the three that Mathlib uses throughout. It does not certify that the statements express the
intended mathematics, nor that `BugeaudHyp` agrees with the published theorem; these are matters of reading
(see "What rests on the written proof or on reading" below).

### Checked by the Lean kernel

- `Collatz.M1.m1_main`, `CollatzND.m1_sigma` and `CollatzND.m1_divergent`, each as an implication
  `BugeaudHyp → …`; also `Collatz.M1.sigma_main` and `Collatz.M1.divergent_count` (which take the Rhin-type bound
  `RhinHyp` as a further hypothesis) and `CollatzND.rhinHyp_holds` (which proves `RhinHyp`).
- The bridge `Collatz.M1.Bugeaud.bugeaudHyp_of_thm2 : Thm2 8 4 → BugeaudHyp` from a Lean transcription of
  Bugeaud's Theorem 2 to the hypothesis (see below).
- The specification tests of `CollatzProof/M1/Spec.lean` (see below).

### The hypotheses `BugeaudHyp` and `RhinHyp`

- **`BugeaudHyp` is an explicit hypothesis, not an axiom.** It is a `Prop`-valued definition
  (`CollatzProof/M1/DeepDefs.lean`) stating Theorem 2 of Y. Bugeaud, *Linear forms in two m-adic logarithms and
  applications to Diophantine problems*, Compositio Math. 132 (2002), 137-158, in the case $m = 8$, $\mu = 4$,
  multiplicatively independent rationals, $c_2(4) = 53.6$, with the narrower side condition "$b_2$ odd". Every
  main theorem takes `hBug : BugeaudHyp` as an argument, so what is proved is the implication `BugeaudHyp → …`.
  `#print axioms` lists axioms only, not hypotheses, so `BugeaudHyp` does not appear in its output. It is used in
  exactly one place, `Collatz.M1.hgt` (`CollatzProof/M1/S13.lean`, the height condition (HGT)). The docstring of
  `BugeaudHyp` lists the hypotheses of the original theorem and how they are transcribed. If the transcription
  were false the main theorems would be vacuous, so the statement of `BugeaudHyp` should be compared with the
  original paper.
- **The bridge to the published theorem.** `CollatzProof/M1/BugeaudBridge.lean` states Theorem 2 of Bugeaud
  (2002) for general $m$ and $\mu$, as a transcription of the original (`Collatz.M1.Bugeaud.Thm2`), and proves in
  the kernel `bugeaudHyp_of_thm2 : Thm2 8 4 → BugeaudHyp`. The proof goes through `bugeaudHyp_of_thm2C2Narrow`,
  whose premise has the extra condition `p ∤ b₂` of Bugeaud's Theorem 1 (which the proof of his Theorem 2 uses),
  so the bridge holds under either reading. The header of the file lists the correspondence with the original
  (pp. 138-140) and the choices made in the Lean statement. The file is not imported by the proofs of the main
  theorems; composing the two implications, the main theorems hold under `Thm2 8 4`. `#print axioms` for
  `bugeaudHyp_of_thm2` reports only the three standard axioms
  (`verify/leanchecker-fresh-BugeaudBridge-2026-09-27.log`). The paper states this derivation as a proposition in
  its Appendix B and gives the correspondence with the original item by item there.
- **`RhinHyp` is proved.** `Collatz.M1.sigma_main` and `Collatz.M1.divergent_count` also assume the Rhin-type
  bound `RhinHyp` ($\lVert q \log_2 3 \rVert \ge C q^{-\kappa}$ for all $q \ge 1$). `CollatzND.rhinHyp_holds`
  proves it from `Erdos1135.ND.existsPhaseGapRhin` of Mazur's formalization ($\kappa = 13.3$), and
  `CollatzND.m1_sigma`, `CollatzND.m1_divergent` are the resulting statements with `BugeaudHyp` as the only
  hypothesis.

### Axioms

`#print axioms` for `Collatz.M1.m1_main`, `Collatz.M1.sigma_main`, `Collatz.M1.divergent_count`,
`CollatzND.rhinHyp_holds`, `CollatzND.m1_sigma` and `CollatzND.m1_divergent` reports only

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

- **The transcription of Bugeaud's theorem.** Whether `Thm2` (and hence `BugeaudHyp`) says what the printed
  Theorem 2 of Bugeaud (2002) says is a matter of reading, not of the kernel. The transcription was compared with
  the primary source in an independent review.
- **The meaning of the statements.** The main statements and the definitions occurring in them (printed above) are
  short enough to be read directly; the specification tests check them on small values.
- **The explicit constants.** The explicit value $\varepsilon(0.6) = 5.35 \times 10^{-14}$ and the other explicit
  constants of the paper rest on the written proof, not on Lean. `verify/proof_pf_certified.py` certifies the 195
  numerical claims behind them with rigorous interval arithmetic in exact rational numbers.

### Review status

The work has not yet been reviewed by independent human experts; no human mathematician has reviewed the proofs.
Formal verification does not replace independent review of the exposition or of the correspondence between the
informal and formal statements.

## Repository layout

| Path | Content |
|---|---|
| `CollatzProof/Core/Defs.lean`, `CollatzProof/Defs.lean` | The shortcut map `T` (in `Core/Defs.lean`, shared with another development of the source repository), the number of odd steps `o`, the additive term `c`, the dual Terras identity $2^j T^j(n) = 3^{o_j} n + c_j$. |
| `CollatzProof/Fiber.lean` | Terras injectivity (parity words of length $t$ determine $n < 2^t$) and fiber bounds. |
| `CollatzProof/M1/Defs.lean`, `Basics.lean`, `Counting.lean` | Notation of Section 3 of the paper (words, heights, survival, slices), common results of Sections 3-4, counting. |
| `CollatzProof/M1/S4.lean` ... `S14.lean` | One file per section: `S4` Theorem A and Corollary A (Section 6 of the paper), `S5` Theorem B (Section 7), `S6` counting swap blocks (Section 8), `S7` shallow frequencies (Section 9), `S9` outer shells (Section 11), `S10` Hölder reduction (Section 12), `S11` physical side and Bhattacharyya coefficients (Sections 13-14), `S13` the height condition (HGT) (Section 15; the only use of `BugeaudHyp`), `S14` assembly and `m1_main` (Section 16). The tools for the phases (Section 10) are in `Phase.lean`. |
| `CollatzProof/M1/Sigma.lean` | Section 17: transfer to the stopping time $\sigma$ (`sigma_main`, `divergent_count`, under `RhinHyp`). |
| `CollatzProof/M1/Spec.lean` | Specification tests for the definitions in the statements (see "Specification tests"); not used by any proof. |
| `CollatzProof/M1/{Fourier,ShellDefs,DeepDefs}.lean` | Definitions: Fourier transform and condition (WF); swap blocks, shells, depth; deep frequencies, lattice condition, `BugeaudHyp`. |
| `CollatzProof/M1/BugeaudBridge.lean` | Theorem 2 of Bugeaud (2002) stated for general $m$ and $\mu$ as in the original (`Collatz.M1.Bugeaud.Thm2`), and the kernel-checked bridge `bugeaudHyp_of_thm2 : Thm2 8 4 → BugeaudHyp`, which goes through `bugeaudHyp_of_thm2C2Narrow` (premise with the extra condition `p ∤ b₂` of Bugeaud's Theorem 1, which the proof of his Theorem 2 uses), so the bridge holds under either reading (not imported by the proofs of the main theorems). |
| `CollatzProof/M1/{C,D,E,G,I,K}_*.lean` | Auxiliary lemmas, grouped by the work package named by the prefix (C: Sections 4-6, D: Theorem B of Section 7, E: Section 8, G: Sections 10-11, I: Sections 13-14, K: Section 16; the `J_` lemmas of Section 15 are in `S13.lean`). |
| `CollatzProof/M1/Compat.lean` | Replacements for lemmas whose names differ between Lean/Mathlib v4.30.0-rc2 and v4.34.1 (the same sources build with both). |
| `CollatzND/Rhin.lean` | Mazur's Rhin-type phase gap rewritten in the form of `RhinHyp`. |
| `CollatzND/M1Sigma.lean` | `rhinHyp_holds`, `m1_sigma`, `m1_divergent` (only `BugeaudHyp` remains). |
| `verify/Probe.lean` | Prints the statements, the definitions used in them, and the axioms (not part of any library). |
| `verify/proof_pf_certified.py` | Certifies, with rigorous interval arithmetic in exact rational numbers (Python standard library, about 13 s), the 195 numerical claims behind the explicit constants of the paper (e.g. $\varepsilon(0.6) \ge 5.35 \times 10^{-14}$). These numbers are not formalized in Lean. Run `python3 verify/proof_pf_certified.py`; it prints one line per claim and a summary, and exits with code 1 if any claim fails. |
| `verify/*.log` | Verification records (see "Verification records"). |
| `fetch_mazur.py` | Downloads Mazur's formalization and checks SHA-256 hashes. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake project (Lean v4.30.0-rc2, Mathlib v4.30.0-rc2). |
| `MANIFEST.sha256` | SHA-256 of every file in this repository except itself. |
| `README.md`, `LICENSE`, `NOTICE` | This file; the Apache License, Version 2.0; the copyright and third-party notice. |

Section numbers in the file names (`S4` ... `S14`) and in the comments of the Lean sources follow an earlier
numbering of the proof: section §k there is Section k+2 of the paper, and §14.5 there is Section 17. The numbers of
individual statements in the comments follow the same earlier numbering and may differ from those of the paper.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain in `lean-toolchain`, Lean v4.30.0-rc2, is
installed automatically), `git`, Python 3 (standard library only). In the root directory of a clone of this
repository:

```sh
sha256sum -c MANIFEST.sha256    # optional: compare every file with its SHA-256 in the manifest
python3 fetch_mazur.py          # Mazur's formalization -> vendor/mazur   (ZIP and per-file SHA-256 checked)
lake exe cache get              # Mathlib v4.30.0-rc2 cache
lake build                      # builds CollatzProof and CollatzND (and the needed part of Mazur's formalization)
lake env lean verify/Probe.lean                      # statements, definitions and axioms
lake env leanchecker --fresh CollatzND.M1Sigma       # re-check every declaration incl. Mathlib in the kernel (30+ minutes)
lake env leanchecker --fresh CollatzProof.M1.BugeaudBridge   # the same for the bridge to Bugeaud's theorem (30+ minutes)
python3 verify/proof_pf_certified.py                 # certify the explicit constants (about 13 s; not Lean)
```

`lake build` also builds `CollatzProof/M1/Spec.lean` (the specification tests) and
`CollatzProof/M1/BugeaudBridge.lean`. Mazur's formalization is not redistributed here; `fetch_mazur.py` downloads
it from its original location and verifies it by hash: L. Mazur, *Natural-density Collatz descent in logarithmic
time*, Lean formalization hosted by ProofAtlas, commit `ca3dd0d63920411213403092aecc6946619eb082`, ZIP SHA-256
`5761e6bdad1284275f3a19aa51d8278a68b19cb569c516c20df956e6fac91864` (Apache-2.0). Only the import closure of
`Erdos1135.ND.RhinPhaseGap` is used.

## Versions

Lean v4.30.0-rc2 (`lean-toolchain`) and Mathlib tag v4.30.0-rc2 (pinned by `lake-manifest.json`). This release
candidate is the version of Mazur's formalization, which is needed to prove `RhinHyp`; with the same toolchain the
stopping-time statements have `BugeaudHyp` as their only hypothesis. The files under `CollatzProof/` also build
with Lean v4.34.1 and Mathlib v4.34.1 in the source repository (that build states the stopping-time results with
`RhinHyp` as a hypothesis); `CollatzProof/M1/Compat.lean` replaces the lemmas whose names differ between the two
versions.

## Verification records

`leanchecker --fresh` re-checks every declaration of the dependency closure, including Mathlib, in the kernel. It
was run on the original sources (Japanese comments, identical code) in the source repository on 2026-09-25, and on
a fresh copy of the files of this repository on 2026-09-26 (exit code 0, 33 minutes, after the shortcut map `T` was
moved to `CollatzProof/Core/Defs.lean`). The logs are in `verify/`:

| Log | Content |
|---|---|
| `manifest-check-2026-09-26.log` | `sha256sum -c MANIFEST.sha256` in the fresh copy of 2026-09-26. |
| `lake-build-2026-09-26.log` | `lake build` in that copy. |
| `probe-2026-09-26.log` | Output of `verify/Probe.lean` in that copy. |
| `leanchecker-fresh-M1Sigma-2026-09-26.log` | `lake env leanchecker --fresh CollatzND.M1Sigma` in that copy (exit code 0). |
| `leanchecker-fresh-BugeaudBridge-2026-09-27.log` | `lake env leanchecker --fresh CollatzProof.M1.BugeaudBridge` in the source repository on 2026-09-27 (Lean v4.30.0-rc2, identical code; exit code 0, 32 minutes), with the axioms of `bugeaudHyp_of_thm2`. |

The Mathlib packages of the 2026-09-26 copy were taken from a local build of the same Mathlib tag instead of
`lake exe cache get`, and Mazur's formalization was downloaded with `fetch_mazur.py`. `BugeaudBridge.lean` and its
log were added on 2026-09-27, after that run; since then `README.md` and `MANIFEST.sha256` have been updated and
`LICENSE` and `NOTICE` added, and the other files are unchanged. The manifest check of 2026-09-26 therefore refers
to the manifest of that time.

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
- Theorem 2 of Bugeaud (2002) is not formalized; it enters only as the hypothesis `BugeaudHyp`
  (`BugeaudBridge.lean` transcribes its statement; it does not prove it).
- All code of this project (the Lean sources in `CollatzProof/` and `CollatzND/`, `verify/Probe.lean`, and the
  Python scripts) was written with Anthropic's Claude models through Claude Code, directed by the author. The Lean
  proofs are checked by the Lean kernel, and this check does not depend on how the code was produced. No human
  mathematician has reviewed the proofs.
- The comments were translated from Japanese. The code is identical to the checked originals: a script in the
  source repository (`check_lean_bundle.py`, in the directory of the paper) confirms that, after removing comments,
  every Lean file except `verify/Probe.lean` (which exists only here) is byte-for-byte identical to its original.
