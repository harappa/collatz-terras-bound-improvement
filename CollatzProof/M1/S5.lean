import CollatzProof.M1.Counting
import CollatzProof.M1.D_Main

/-! # §5: Theorem B (from the shell bounds to (WF))

The components of the proof are in auxiliary files (prefix `D_`).
- `D_Word`: recursion for the number of 1s, exchange of swap blocks, the closed form of `c_x` and its change under the exchange.
- `D_Fourier`: properties of `e(x)`, Parseval, the coefficients `ω` of Lemma 5.1 and the expansion, periodic sums over a shell.
- `D_Orbit`: averages over swap orbits (the abstract form of Lemma 5.3 (iii)).
- `D_Slice`: Lemma 3.3 (the form and range of `G`), Lemma 5.3 (the exchange preserves `𝒯` and `ℬ`, and the phase is `θ_b(N)`).
- `D_CRT`: indexing by the Chinese remainder theorem (§5.1) and the expansion of `Ĝ`.
- `D_Main`: Lemma 5.5 (reduction) and `Λ_{L,P} ≤ 4(L+1)² 2^q B/|E|`.
Instead of `Γ_L = 3 + L ln 3` of the manuscript we use `Σ_η |ω_ξ(η)| ≤ 2(L+1)` (a factor polynomial in `q`, so the same in the qualitative form).
The general form `thmBG` (`RdeltaG a b δ`, `WFG a b δ`, `aδ ≤ 1.23×10^{−3}`, `bδ² ≤ 3.5×10^{−6}`) is stated, and `thmB` of version 2 is its special case (for version 3 of the proof manuscript).
-/

namespace Collatz.M1

open Finset

/-! ## Numerical auxiliaries -/

/-- If the tail is nonempty, then `L_p < L`. -/
lemma D_Lp_lt {q s L P : ℕ} (hTne : (Tset q s L P).Nonempty) (ht : 0 < s - P) : Lp q + 1 ≤ L := by
  obtain ⟨τ, hτ⟩ := hTne
  obtain ⟨h0, h1, _⟩ := D_mem_Tset.mp hτ
  have e := D_ones_succ τ 0
  rw [D_ones_zero, D_xb_lt τ ht, h0 ht] at e
  have hm := D_ones_mono τ (show 1 ≤ s - P by omega)
  simp only [ite_true, zero_add] at e
  omega

/-- From `2^q < 3^{L_p+1}`, `q < λ(L_p + 1)`. -/
lemma D_q_lt_lam (q : ℕ) : (q : ℝ) < lam * (Lp q + 1) := by
  have h := (Lp_spec q).2
  have h' : (2 : ℝ) ^ (q : ℝ) < (2 : ℝ) ^ (lam * (Lp q + 1)) := by
    rw [Real.rpow_natCast, Real.rpow_mul (by norm_num), lam,
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      show ((Lp q : ℝ) + 1) = ((Lp q + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact_mod_cast h
  exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp h'

/-- General form of Lemma 3.3 (iii): if `s ≤ 1.94q`, `q ≥ 67` and `h_p ≤ 1.23×10^{−3}q`, then `2^t < 3^{L_p}`
(version 2 obtains the last condition from `h_p ≤ 1.23δq`, `δ ≤ 10^{−3}`, version 3 from `h_p ≤ 1.38δq`, `δ ≤ 10^{−4}`). -/
lemma D_two_pow_lt' {q s P : ℕ} (hq : 67 ≤ q) (hs : (s : ℝ) ≤ 1.94 * q) (hp1 : hp q P ≤ 1.23e-3 * q)
    (hPs : P < s) : 2 ^ (s - P) < 3 ^ Lp q := by
  have hlam := lam_bounds
  have hqlam := D_q_lt_lam q
  unfold hp at hp1
  have hq' : (67 : ℝ) ≤ q := by exact_mod_cast hq
  have hts : ((s - P : ℕ) : ℝ) = s - P := by rw [Nat.cast_sub hPs.le]
  have key : ((s - P : ℕ) : ℝ) < lam * Lp q := by
    rw [hts]; nlinarith
  have h' : (2 : ℝ) ^ ((s - P : ℕ) : ℝ) < (2 : ℝ) ^ (lam * Lp q) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) key
  rw [Real.rpow_natCast, Real.rpow_mul (by norm_num), lam,
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast] at h'
  exact_mod_cast h'

-- The hypothesis `hδ` is not needed once the proof goes through the general form `D_two_pow_lt'` (the statement of the skeleton is kept).
set_option linter.unusedVariables false in
/-- Lemma 3.3 (iii): if `δ ≤ 10^{−3}`, `s ≤ 1.94q`, `q ≥ 67`, `h_p ≤ 1.23δq`, then `2^t < 3^{L_p}`. -/
lemma D_two_pow_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) {q s P : ℕ} (hq : 67 ≤ q)
    (hs : (s : ℝ) ≤ 1.94 * q) (hp1 : hp q P ≤ 1.23 * δ * q) (hPs : P < s) :
    2 ^ (s - P) < 3 ^ Lp q := by
  have hδq : 1.23 * δ * q ≤ 1.23e-3 * q := by
    apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
  exact D_two_pow_lt' hq hs (hp1.trans hδq) hPs

/-- On the slices of `R_δ`, `L + 1 ≤ 2q` (general form: from `h_L ≤ 3.5×10^{−6}q`). -/
lemma D_L_bound' {q s L : ℕ} (hq : 2 ≤ q) (hs : (s : ℝ) ≤ 1.94 * q) (hL1 : hL s L ≤ 3.5e-6 * q) :
    (L : ℝ) + 1 ≤ 2 * q := by
  have hlam := lam_bounds
  unfold hL at hL1
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hLl : 1.5849 * (L : ℝ) ≤ lam * L := mul_le_mul_of_nonneg_right hlam.1.le (by positivity)
  nlinarith

/-- On the slices of `R_δ`, `L + 1 ≤ 2q`. -/
lemma D_L_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) {q s L : ℕ} (hq : 2 ≤ q)
    (hs : (s : ℝ) ≤ 1.94 * q) (hL1 : hL s L ≤ 3.5 * δ ^ 2 * q) : (L : ℝ) + 1 ≤ 2 * q := by
  have hδ2 : 3.5 * δ ^ 2 ≤ 3.5e-6 := by nlinarith
  exact D_L_bound' hq hs (hL1.trans (mul_le_mul_of_nonneg_right hδ2 (by positivity)))

/-- `C q^4 ≤ 2^{εq}` (for sufficiently large `q`). -/
lemma D_asymp (ε : ℝ) (hε : 0 < ε) :
    ∃ q1 : ℕ, ∀ q : ℕ, q1 ≤ q → (2 : ℝ) ^ 7 * (q : ℝ) ^ 4 ≤ (2 : ℝ) ^ (ε * q) := by
  have hb : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  have h := (isLittleO_pow_exp_pos_mul_atTop 4 hb).bound (show (0 : ℝ) < 1 / 2 ^ 7 by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp h
  refine ⟨⌈X⌉₊, fun q hq => ?_⟩
  have hqX : X ≤ (q : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hq)
  have := hX q hqX
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at this
  rw [Real.rpow_def_of_pos (by norm_num)]
  have e : Real.log 2 * (ε * q) = ε * Real.log 2 * q := by ring
  rw [e]
  have h7 : (0 : ℝ) < 2 ^ 7 := by positivity
  calc (2 : ℝ) ^ 7 * (q : ℝ) ^ 4 ≤ 2 ^ 7 * (1 / 2 ^ 7 * Real.exp (ε * Real.log 2 * q)) :=
        mul_le_mul_of_nonneg_left this h7.le
    _ = Real.exp (ε * Real.log 2 * q) := by field_simp

/-- The final real-number estimate of Theorem B. -/
lemma D_final_real (q : ℕ) (hq : 1 ≤ q) (c δ δ' Lr Er Λ : ℝ)
    (hE : (2 : ℝ) ^ ((1 - c) * q - 1.1) / (q * (q + 1)) ≤ Er) (hLr : Lr + 1 ≤ 2 * q)
    (hLr0 : 0 ≤ Lr) (hΛ : Λ ≤ 4 * (Lr + 1) ^ 2 * (2 : ℝ) ^ q * (2 : ℝ) ^ (-(δ' * q)) / Er)
    (hasym : (2 : ℝ) ^ 7 * (q : ℝ) ^ 4 ≤ (2 : ℝ) ^ ((δ' - 2 * δ) * q)) :
    Λ ≤ (2 : ℝ) ^ ((c - 2 * δ) * q) := by
  set x := (2 : ℝ) ^ ((1 - c) * q - 1.1) with hx
  have hxpos : 0 < x := by positivity
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hEpos : 0 < Er := lt_of_lt_of_le (by positivity) hE
  set Y := (2 : ℝ) ^ q * (2 : ℝ) ^ (-(δ' * q)) with hY
  have hYpos : 0 < Y := by positivity
  have e1 : Y / x = (2 : ℝ) ^ (1.1 : ℝ) * (2 : ℝ) ^ ((c - δ') * q) := by
    rw [hY, hx, ← Real.rpow_natCast, ← Real.rpow_add two_pos, ← Real.rpow_sub two_pos,
      ← Real.rpow_add two_pos]
    congr 1; ring
  have e2 : (2 : ℝ) ^ ((δ' - 2 * δ) * q) * (2 : ℝ) ^ ((c - δ') * q) = (2 : ℝ) ^ ((c - 2 * δ) * q) := by
    rw [← Real.rpow_add two_pos]; congr 1; ring
  have h11 : (2 : ℝ) ^ (1.1 : ℝ) ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) (show (1.1 : ℝ) ≤ 2 by norm_num)
    rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at this
    exact this
  have hinvE : 1 / Er ≤ (q * (q + 1)) / x := by
    rw [div_le_div_iff₀ hEpos hxpos, one_mul]
    rw [div_le_iff₀ (by positivity)] at hE
    linarith
  have hL2 : (Lr + 1) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by nlinarith
  have hqq : (q : ℝ) * (q + 1) ≤ 2 * (q : ℝ) ^ 2 := by nlinarith
  have hZ : 0 < (2 : ℝ) ^ ((c - δ') * q) := by positivity
  calc Λ ≤ 4 * (Lr + 1) ^ 2 * (2 : ℝ) ^ q * (2 : ℝ) ^ (-(δ' * q)) / Er := hΛ
    _ = 4 * (Lr + 1) ^ 2 * Y * (1 / Er) := by rw [hY]; ring
    _ ≤ 4 * (Lr + 1) ^ 2 * Y * ((q * (q + 1)) / x) := by gcongr
    _ = 4 * (Lr + 1) ^ 2 * (q * (q + 1)) * (Y / x) := by ring
    _ ≤ 4 * (4 * (q : ℝ) ^ 2) * (2 * (q : ℝ) ^ 2) * (4 * (2 : ℝ) ^ ((c - δ') * q)) := by
        rw [e1]; gcongr
    _ = (2 : ℝ) ^ 7 * (q : ℝ) ^ 4 * (2 : ℝ) ^ ((c - δ') * q) := by ring
    _ ≤ (2 : ℝ) ^ ((δ' - 2 * δ) * q) * (2 : ℝ) ^ ((c - δ') * q) := by gcongr
    _ = _ := e2

/-- General form of Theorem B (`RdeltaG a b δ`): let `1 < s/q ≤ 1.94`, `aδ ≤ 1.23×10^{−3}`, `bδ² ≤ 3.5×10^{−6}` and `δ' > 2δ`.
If `q` is sufficiently large and `A_k ≤ 2^{−δ'q}` for every slice of `RdeltaG a b δ` and every shell `0 ≤ k ≤ L`, then `WFG a b δ`.
Version 2 has `(a, b) = (1.23, 3.5)`, `δ ≤ 10^{−3}` (`thmB`), version 3 has `(a, b) = (1.38, 4.48)`, `δ ≤ 10^{−4}` (§4.2.3 of version 3 of the manuscript). -/
theorem thmBG (a b δ δ' : ℝ) (haδ : a * δ ≤ 1.23e-3) (hbδ : b * δ ^ 2 ≤ 3.5e-6) (hδ' : 2 * δ < δ') :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 →
      (∀ L P, RdeltaG a b δ s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q))) →
        WFG a b δ s q := by
  obtain ⟨q1, hq1⟩ := D_asymp (δ' - 2 * δ) (by linarith)
  refine ⟨max q1 67, fun s q hq _ hs2 hA => ?_⟩
  intro L P hR
  have hq67 : 67 ≤ q := le_of_max_le_right hq
  have hqq1 : q1 ≤ q := le_of_max_le_left hq
  have hqpos : (0 : ℝ) < q := by
    have : (67 : ℝ) ≤ q := by exact_mod_cast hq67
    linarith
  have hs : (s : ℝ) ≤ 1.94 * q := by rwa [div_le_iff₀ hqpos] at hs2
  have hAk := hA L P hR
  obtain ⟨hL0, hL1, _, hp1, _, hTne, hPs⟩ := hR
  have hp1' : hp q P ≤ 1.23e-3 * q := hp1.trans (mul_le_mul_of_nonneg_right haδ hqpos.le)
  have hL1' : hL s L ≤ 3.5e-6 * q := hL1.trans (mul_le_mul_of_nonneg_right hbδ hqpos.le)
  have ht : 0 < s - P := by omega
  have hLp : Lp q ≤ L := by have := D_Lp_lt hTne ht; omega
  have h2t := D_two_pow_lt' hq67 hs hp1' hPs
  have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (-(δ' * q)) := by positivity
  have hLam := D_LamLP_le (by omega) hLp ht h2t hTne _ hB hAk
  have hE := E_lower q (by omega) (hL s L) hL0
  have hLq := D_L_bound' (by omega) hs hL1'
  exact D_final_real q (by omega) cc δ δ' L _ _ hE hLq (by positivity) (by simpa [mul_assoc] using hLam)
    (hq1 q hqq1)

/-- Theorem B: let `1 < s/q ≤ 1.94`, `0 < δ ≤ 10^{−3}`, `δ' > 2δ`. If `q` is sufficiently large (depending on `δ, δ'`) and
`A_k ≤ 2^{−δ'q}` for every slice of `R_δ` and every shell `0 ≤ k ≤ L`, then (WF)(δ). -/
theorem thmB (δ δ' : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) (hδ' : 2 * δ < δ') :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 →
      (∀ L P, Rdelta δ s q L P → ∀ k ≤ L, Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q))) → WF δ s q :=
  thmBG 1.23 3.5 δ δ' (by linarith) (by nlinarith) hδ'

end Collatz.M1
