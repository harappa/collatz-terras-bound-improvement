import CollatzProof.M1.Defs

/-!
# Auxiliary results for §6: elementary properties of the constants, and the model with independent letters

We prove Lemma 6.1 (one step) and steps 2 and 3 of Lemma 6.2 (the successive estimate over the windows in the model with independent letters)
in a general form that does not depend on `𝒯` (used in `window_count` of `S6.lean`).
- The weight `E_nu p x` in which the letter at position `i` of the word `x : Fin n → Bool` is 1 independently with probability `p i`.
- The factor `E_blk` of the block at positions `(j, j+1)` (the `φ_γ` of Lemma 6.1: valid (nonzero) if the two heights inside the block are at least 0,
  and `γ` if the height just before is at least 1 and the block is `01` or `10`).
- Main result `E_GL`: for the `m` blocks at positions `j₀, j₀+2, …`, `𝔼 Π φ_γ ≤ Θ_γ(ρ)^m` (the probability inside the window is `ρ`).
-/

namespace Collatz.M1

open Finset

/-! ## Auxiliary: elementary properties of the constants and of `L_p` -/

theorem E_lam_gt_one : 1 < lam := by
  unfold lam
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  norm_num

theorem E_lam_lt_two : lam < 2 := by
  unfold lam
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
  norm_num

theorem E_aa_pos : 0 < aa := by
  unfold aa; linarith [E_lam_gt_one]

theorem E_rhoc_gt_half : 1 / 2 < rhoc := by
  unfold rhoc
  exact one_div_lt_one_div_of_lt (by linarith [E_lam_gt_one]) E_lam_lt_two

theorem E_Lp_pow (q : ℕ) : 3 ^ Lp q ≤ 2 ^ q := by
  unfold Lp
  exact Nat.findGreatest_spec (P := fun l => 3 ^ l ≤ 2 ^ q) (Nat.zero_le q) (by simpa using Nat.one_le_two_pow)

theorem E_lam_Lp_le (q : ℕ) : lam * (Lp q : ℝ) ≤ q := by
  have h : ((3:ℝ) ^ Lp q) ≤ (2:ℝ) ^ q := by exact_mod_cast E_Lp_pow q
  have h2 := (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).2 h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  unfold lam; linarith

theorem E_ones_pos {n : ℕ} (x : Fin n → Bool) (h0 : 0 < n) (hx : x ⟨0, h0⟩ = true) (j : ℕ)
    (hj : 1 ≤ j) : 1 ≤ ones x j := by
  classical
  unfold ones
  apply Finset.card_pos.2
  exact ⟨⟨0, h0⟩, by simp [hx]; omega⟩


/-! ## Auxiliary: the model with independent letters (Lemmas 6.1 and 6.2, steps 2 and 3) -/

theorem E_sum_cons {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ x : Fin (n+1) → Bool, f x = ∑ b : Bool, ∑ x : Fin n → Bool, f (Fin.cons b x) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem E_ones_zero {n : ℕ} (x : Fin n → Bool) : ones x 0 = 0 := by
  simp [ones]

theorem E_ones_cons {n : ℕ} (b : Bool) (x : Fin n → Bool) (j : ℕ) :
    ones (Fin.cons b x : Fin (n+1) → Bool) (j+1) = (if b then 1 else 0) + ones x j := by
  classical
  unfold ones
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

/-- The letter of a word, taken to be `false` out of range. -/
def E_xa {n : ℕ} (x : Fin n → Bool) (j : ℕ) : Bool := if h : j < n then x ⟨j, h⟩ else false

/-- The weight of a word in the model with independent letters with position-dependent probability `p`. -/
noncomputable def E_nu (p : ℕ → ℝ) {n : ℕ} (x : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, (if x i then p i else 1 - p i)

/-- The height increment of one letter (`a` for 1, `−1` for 0). -/
noncomputable def E_dl (b : Bool) : ℝ := lam * (if b then 1 else 0) - 1

/-- `φ_γ(h, b₁b₂)` of Lemma 6.1. -/
noncomputable def E_phi (γ h : ℝ) (b₁ b₂ : Bool) : ℝ :=
  if 0 ≤ h + E_dl b₁ ∧ 0 ≤ h + E_dl b₁ + E_dl b₂ then (if 1 ≤ h ∧ b₁ ≠ b₂ then γ else 1) else 0

/-- The factor of the block at positions `(j, j+1)` (heights counted from `y`). -/
noncomputable def E_blk (γ y : ℝ) {n : ℕ} (x : Fin n → Bool) (j : ℕ) : ℝ :=
  if 0 ≤ hw y x (j+1) ∧ 0 ≤ hw y x (j+2) then
    (if 1 ≤ hw y x j ∧ E_xa x j ≠ E_xa x (j+1) then γ else 1) else 0

/-- The product of the factors of the `m` blocks starting at positions `j₀, j₀+2, …`. -/
noncomputable def E_W (γ y : ℝ) {n : ℕ} (x : Fin n → Bool) (j₀ m : ℕ) : ℝ :=
  ∏ i ∈ range m, E_blk γ y x (j₀ + 2 * i)

theorem E_xa_cons_zero {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    E_xa (Fin.cons b x : Fin (n+1) → Bool) 0 = b := by
  simp [E_xa]

theorem E_xa_cons_succ {n : ℕ} (b : Bool) (x : Fin n → Bool) (j : ℕ) :
    E_xa (Fin.cons b x : Fin (n+1) → Bool) (j+1) = E_xa x j := by
  unfold E_xa
  by_cases h : j < n
  · rw [dif_pos (show j + 1 < n + 1 by omega), dif_pos h]
    exact Fin.cons_succ (α := fun _ => Bool) b x ⟨j, h⟩
  · rw [dif_neg (by omega), dif_neg h]

theorem E_hw_zero {n : ℕ} (y : ℝ) (x : Fin n → Bool) : hw y x 0 = y := by
  simp [hw, E_ones_zero]

theorem E_hw_cons {n : ℕ} (y : ℝ) (b : Bool) (x : Fin n → Bool) (j : ℕ) :
    hw y (Fin.cons b x : Fin (n+1) → Bool) (j+1) = hw (y + E_dl b) x j := by
  unfold hw E_dl
  rw [E_ones_cons]
  cases b <;> simp <;> ring

theorem E_nu_cons (p : ℕ → ℝ) {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    E_nu p (Fin.cons b x : Fin (n+1) → Bool) =
      (if b then p 0 else 1 - p 0) * E_nu (fun i => p (i+1)) x := by
  unfold E_nu
  rw [Fin.prod_univ_succ]
  simp

theorem E_blk_cons (γ y : ℝ) {n : ℕ} (b : Bool) (x : Fin n → Bool) (j : ℕ) :
    E_blk γ y (Fin.cons b x : Fin (n+1) → Bool) (j+1) = E_blk γ (y + E_dl b) x j := by
  have h1 : hw y (Fin.cons b x : Fin (n+1) → Bool) (j+1) = hw (y + E_dl b) x j := E_hw_cons y b x j
  have h2 : hw y (Fin.cons b x : Fin (n+1) → Bool) (j+1+1) = hw (y + E_dl b) x (j+1) :=
    E_hw_cons y b x (j+1)
  have h3 : hw y (Fin.cons b x : Fin (n+1) → Bool) (j+1+2) = hw (y + E_dl b) x (j+2) :=
    E_hw_cons y b x (j+2)
  have h4 := E_xa_cons_succ b x j
  have h5 : E_xa (Fin.cons b x : Fin (n+1) → Bool) (j+1+1) = E_xa x (j+1) := E_xa_cons_succ b x (j+1)
  unfold E_blk
  rw [h1, h2, h3, h4, h5]

theorem E_blk_cons2 (γ y : ℝ) {n : ℕ} (b₁ b₂ : Bool) (x : Fin n → Bool) :
    E_blk γ y (Fin.cons b₁ (Fin.cons b₂ x : Fin (n+1) → Bool) : Fin (n+2) → Bool) 0 =
      E_phi γ y b₁ b₂ := by
  unfold E_blk E_phi
  rw [show (0:ℕ) + 1 = 0 + 1 from rfl, E_hw_cons, E_hw_zero, show (0:ℕ) + 2 = 1 + 1 from rfl,
    E_hw_cons, E_hw_cons, E_hw_zero, E_hw_zero, E_xa_cons_zero, E_xa_cons_succ, E_xa_cons_zero]

theorem E_W_cons (γ y : ℝ) {n : ℕ} (b : Bool) (x : Fin n → Bool) (j₀ m : ℕ) :
    E_W γ y (Fin.cons b x : Fin (n+1) → Bool) (j₀ + 1) m = E_W γ (y + E_dl b) x j₀ m := by
  unfold E_W
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show j₀ + 1 + 2 * i = (j₀ + 2 * i) + 1 by ring, E_blk_cons]

theorem E_W_succ (γ y : ℝ) {n : ℕ} (x : Fin n → Bool) (j₀ m : ℕ) :
    E_W γ y x j₀ (m + 1) = E_blk γ y x j₀ * E_W γ y x (j₀ + 2) m := by
  unfold E_W
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show j₀ + 2 * (i + 1) = j₀ + 2 + 2 * i by ring]

theorem E_nu_sum (p : ℕ → ℝ) (n : ℕ) : ∑ x : Fin n → Bool, E_nu p x = 1 := by
  induction n generalizing p with
  | zero => simp [E_nu]
  | succ n ih =>
    rw [E_sum_cons]
    simp only [E_nu_cons, ← Finset.mul_sum, ih, Fintype.sum_bool]
    simp

theorem E_nu_nonneg (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {n : ℕ} (x : Fin n → Bool) :
    0 ≤ E_nu p x := by
  unfold E_nu
  refine Finset.prod_nonneg (fun i _ => ?_)
  split_ifs
  · exact (hp i).1
  · linarith [(hp i).2]

theorem E_blk_nonneg (γ y : ℝ) (hγ : 0 ≤ γ) {n : ℕ} (x : Fin n → Bool) (j : ℕ) :
    0 ≤ E_blk γ y x j := by
  unfold E_blk
  split_ifs <;> linarith

theorem E_W_nonneg (γ y : ℝ) (hγ : 0 ≤ γ) {n : ℕ} (x : Fin n → Bool) (j₀ m : ℕ) :
    0 ≤ E_W γ y x j₀ m :=
  Finset.prod_nonneg (fun _ _ => E_blk_nonneg γ y hγ x _)

theorem E_dl_true : E_dl true = lam - 1 := by simp [E_dl]
theorem E_dl_false : E_dl false = -1 := by simp [E_dl]

theorem E_phi_tt (γ h : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    0 ≤ E_phi γ h true true ∧ E_phi γ h true true ≤ 1 := by
  unfold E_phi
  split_ifs <;> constructor <;> linarith

theorem E_phi_ff (γ h : ℝ) :
    0 ≤ E_phi γ h false false ∧ E_phi γ h false false ≤ if 1 ≤ h then 1 else 0 := by
  simp only [E_phi, E_dl_false, ne_eq, not_true_eq_false, and_false, ite_false]
  split_ifs with hc hd <;> (try obtain ⟨hc1, hc2⟩ := hc) <;> constructor <;> linarith

theorem E_phi_tf (γ h : ℝ) (hγ0 : 0 ≤ γ) :
    0 ≤ E_phi γ h true false ∧ E_phi γ h true false ≤ if 1 ≤ h then γ else 1 := by
  simp only [E_phi, E_dl_false, E_dl_true, ne_eq, Bool.true_eq_false, not_false_eq_true, and_true]
  split_ifs with hc hd <;> (try obtain ⟨hc1, hc2⟩ := hc) <;> constructor <;> linarith

theorem E_phi_ft (γ h : ℝ) (hγ0 : 0 ≤ γ) :
    0 ≤ E_phi γ h false true ∧ E_phi γ h false true ≤ if 1 ≤ h then γ else 0 := by
  simp only [E_phi, E_dl_false, E_dl_true, ne_eq, Bool.false_eq_true, not_false_eq_true, and_true]
  split_ifs with hc hd <;> (try obtain ⟨hc1, hc2⟩ := hc) <;> constructor <;> linarith

/-- Lemma 6.1 (one step). -/
theorem E_onestep (γ ρ h : ℝ) (hγ1 : 1/2 ≤ γ) (hγ2 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∑ b₁ : Bool, ∑ b₂ : Bool,
      (if b₁ then ρ else 1 - ρ) * ((if b₂ then ρ else 1 - ρ) * E_phi γ h b₁ b₂) ≤ Theta γ ρ := by
  have hγ0 : 0 ≤ γ := by linarith
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  unfold Theta
  have h1ρ : 0 ≤ 1 - ρ := by linarith
  have hρρ : 0 ≤ ρ * (1 - ρ) := mul_nonneg hρ0 h1ρ
  obtain ⟨tt0, tt1⟩ := E_phi_tt γ h hγ0 hγ2
  obtain ⟨ff0, ff1⟩ := E_phi_ff γ h
  obtain ⟨tf0, tf1⟩ := E_phi_tf γ h hγ0
  obtain ⟨ft0, ft1⟩ := E_phi_ft γ h hγ0
  have e1 : ρ * (ρ * E_phi γ h true true) ≤ ρ * ρ := by
    apply mul_le_mul_of_nonneg_left _ hρ0; nlinarith
  by_cases h1 : 1 ≤ h
  · rw [if_pos h1] at ff1 tf1 ft1
    have e2 : ρ * ((1 - ρ) * E_phi γ h true false) ≤ ρ * (1 - ρ) * γ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left tf1 hρρ
    have e3 : (1 - ρ) * (ρ * E_phi γ h false true) ≤ ρ * (1 - ρ) * γ := by
      rw [← mul_assoc, mul_comm (1 - ρ) ρ]; exact mul_le_mul_of_nonneg_left ft1 hρρ
    have e4 : (1 - ρ) * ((1 - ρ) * E_phi γ h false false) ≤ (1 - ρ) * (1 - ρ) := by
      apply mul_le_mul_of_nonneg_left _ h1ρ; nlinarith
    nlinarith
  · rw [if_neg h1] at ff1 tf1 ft1
    have e2 : ρ * ((1 - ρ) * E_phi γ h true false) ≤ ρ * (1 - ρ) := by
      rw [← mul_assoc]; nlinarith
    have e3 : (1 - ρ) * (ρ * E_phi γ h false true) ≤ 0 := by
      have : E_phi γ h false true = 0 := le_antisymm ft1 ft0
      rw [this]; simp
    have e4 : (1 - ρ) * ((1 - ρ) * E_phi γ h false false) ≤ 0 := by
      have : E_phi γ h false false = 0 := le_antisymm ff1 ff0
      rw [this]; simp
    have key : 0 ≤ (1 - ρ) * (1 - 2 * (1 - γ) * ρ) := by
      apply mul_nonneg h1ρ; nlinarith
    nlinarith

theorem E_Theta_nonneg (γ ρ : ℝ) (hγ1 : 1/2 ≤ γ) (hγ2 : γ ≤ 1) : 0 ≤ Theta γ ρ := by
  unfold Theta
  nlinarith [sq_nonneg (ρ - 1/2)]

theorem E_w_nonneg (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (b : Bool) :
    0 ≤ (if b then r else 1 - r) := by
  split_ifs <;> linarith

/-- The window estimate in the model with independent letters (Lemma 6.2, steps 2 and 3). The `m` blocks at positions `j₀, j₀+2, …`. -/
theorem E_GL (γ ρ : ℝ) (hγ1 : 1/2 ≤ γ) (hγ2 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∀ (j₀ m n : ℕ) (y : ℝ) (p : ℕ → ℝ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
      (∀ i, j₀ ≤ i → i < j₀ + 2 * m → p i = ρ) → j₀ + 2 * m ≤ n →
      ∑ x : Fin n → Bool, E_nu p x * E_W γ y x j₀ m ≤ Theta γ ρ ^ m := by
  have hγ0 : 0 ≤ γ := by linarith
  have hΘ := E_Theta_nonneg γ ρ hγ1 hγ2
  intro j₀
  induction j₀ with
  | zero =>
    intro m
    induction m with
    | zero =>
      intro n y p _ _ _
      simp [E_W, E_nu_sum]
    | succ m ih =>
      intro n y p hp hpρ hn
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have hp0 : p 0 = ρ := hpρ 0 le_rfl (by omega)
      have hp1 : p 1 = ρ := hpρ 1 (by omega) (by omega)
      calc ∑ x : Fin (n + 2) → Bool, E_nu p x * E_W γ y x 0 (m + 1)
          = ∑ b₁ : Bool, ∑ b₂ : Bool,
              (if b₁ then ρ else 1 - ρ) * ((if b₂ then ρ else 1 - ρ) * E_phi γ y b₁ b₂) *
              ∑ x : Fin n → Bool, E_nu (fun i => p (i + 1 + 1)) x *
                E_W γ (y + E_dl b₁ + E_dl b₂) x 0 m := by
            rw [E_sum_cons]
            refine Finset.sum_congr rfl (fun b₁ _ => ?_)
            rw [E_sum_cons]
            refine Finset.sum_congr rfl (fun b₂ _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            have e1 := E_W_cons γ y b₁ (Fin.cons b₂ x : Fin (n+1) → Bool) 1 m
            have e2 := E_W_cons γ (y + E_dl b₁) b₂ x 0 m
            rw [E_nu_cons, E_nu_cons, E_W_succ, E_blk_cons2]
            simp only [zero_add] at e1 e2 ⊢
            rw [e1, e2, hp0, hp1]
            ring
        _ ≤ ∑ b₁ : Bool, ∑ b₂ : Bool,
              (if b₁ then ρ else 1 - ρ) * ((if b₂ then ρ else 1 - ρ) * E_phi γ y b₁ b₂) *
              Theta γ ρ ^ m := by
            refine Finset.sum_le_sum (fun b₁ _ => Finset.sum_le_sum (fun b₂ _ => ?_))
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · refine ih n _ _ (fun i => hp (i + 1 + 1)) (fun i _ hi => hpρ _ (by omega) (by omega))
                (by omega)
            · refine mul_nonneg (E_w_nonneg ρ hρ0 hρ1 b₁) (mul_nonneg (E_w_nonneg ρ hρ0 hρ1 b₂) ?_)
              unfold E_phi; split_ifs <;> linarith
        _ = (∑ b₁ : Bool, ∑ b₂ : Bool,
              (if b₁ then ρ else 1 - ρ) * ((if b₂ then ρ else 1 - ρ) * E_phi γ y b₁ b₂)) *
              Theta γ ρ ^ m := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun b₁ _ => ?_)
            rw [Finset.sum_mul]
        _ ≤ Theta γ ρ * Theta γ ρ ^ m :=
            mul_le_mul_of_nonneg_right (E_onestep γ ρ y hγ1 hγ2 hρ0 hρ1) (pow_nonneg hΘ m)
        _ = Theta γ ρ ^ (m + 1) := by ring
  | succ j ih =>
    intro m n y p hp hpρ hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    calc ∑ x : Fin (n + 1) → Bool, E_nu p x * E_W γ y x (j + 1) m
        = ∑ b : Bool, (if b then p 0 else 1 - p 0) *
            ∑ x : Fin n → Bool, E_nu (fun i => p (i + 1)) x * E_W γ (y + E_dl b) x j m := by
          rw [E_sum_cons]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [E_nu_cons, E_W_cons]
          ring
      _ ≤ ∑ b : Bool, (if b then p 0 else 1 - p 0) * Theta γ ρ ^ m := by
          refine Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left ?_
            (E_w_nonneg _ (hp 0).1 (hp 0).2 b))
          exact ih m n _ _ (fun i => hp (i + 1)) (fun i hi1 hi2 => hpρ _ (by omega) (by omega))
            (by omega)
      _ = Theta γ ρ ^ m := by
          simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
          ring

/-! ## Auxiliary: the weight with position 0 fixed (Lemma 6.2, step 4) -/

theorem E_ones_le {n : ℕ} (x : Fin n → Bool) (j : ℕ) : ones x j ≤ n := by
  unfold ones
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The weight with position-independent probability `r`: `r^{|x|}(1−r)^{n−|x|}`. -/
theorem E_nu_const (r : ℝ) : ∀ (n : ℕ) (x : Fin n → Bool),
    E_nu (fun _ => r) x = r ^ (ones x n) * (1 - r) ^ (n - ones x n) := by
  intro n
  induction n with
  | zero => intro x; simp [E_nu, ones]
  | succ n ih =>
    intro x
    rw [← Fin.cons_self_tail x, E_nu_cons, E_ones_cons, ih]
    have hle := E_ones_le (Fin.tail x) n
    generalize x 0 = b
    generalize ones (Fin.tail x) n = o at hle ⊢
    cases b
    · simp only [Bool.false_eq_true, ite_false, zero_add]
      rw [show n + 1 - o = (n - o) + 1 by omega, pow_succ]
      ring
    · simp only [ite_true]
      rw [show n + 1 - (1 + o) = n - o by omega, show 1 + o = o + 1 by ring, pow_succ]
      ring

/-- The weight with the letter at position 0 fixed to 1 and the others of probability `r`: `r^{|x|−1}(1−r)^{n−|x|}`. -/
theorem E_nu_tau (r : ℝ) {n : ℕ} (x : Fin n → Bool) (h0 : 0 < n) (hx : x ⟨0, h0⟩ = true) :
    E_nu (fun i => if i = 0 then 1 else r) x = r ^ (ones x n - 1) * (1 - r) ^ (n - ones x n) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hx0 : x 0 = true := hx
  rw [← Fin.cons_self_tail x, E_nu_cons, E_ones_cons, hx0]
  have hfun : (fun i : ℕ => (if i + 1 = 0 then (1:ℝ) else r)) = fun _ => r := by
    funext i; simp
  simp only [ite_true]
  rw [hfun, E_nu_const]
  rw [show 1 + ones (Fin.tail x) n - 1 = ones (Fin.tail x) n by omega,
    show n + 1 - (1 + ones (Fin.tail x) n) = n - ones (Fin.tail x) n by omega]
  ring

end Collatz.M1
