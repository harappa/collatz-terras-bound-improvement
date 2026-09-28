import CollatzProof.M1.Phase
import CollatzProof.M1.S6
import CollatzProof.M1.G_Riesz

/-!
# §9: the outer shells (unconditional)

Lemma 9.1 (the end zone) is proved in the per-tail form `⟨Π_{b∈ℬ(τ)} cos² πθ_b⟩_k ≤ 2^{−N_d(τ)} + 2^d 3^{−(k−1)}` (`G_shAvg_bound`);
averaging over tails gives `A_k ≤ 𝔼_τ 2^{−N_d} + 2^d 3^{−(k−1)}` (`G_Ak_bound`) (since `A_k` is defined in the form of a tail average, orbits are not needed).
The steps follow the manuscript: fiber representation (Lemma 8.2, `shell_fiber`), rotation within a fiber (`G_cos_theta`), restriction to the window and expansion (`G_riesz_sum`,
`G_Riesz.lean`), lower bound on the frequencies (`G_alpha_sep`: Lemmas 8.1 and 8.5), summation.
Proposition 9.2 takes `d = min(t − 1, d')` and combines this with Lemma 6.2 (`window_count`). The manuscript's "`q` sufficiently large" only needs
`d ≤ q + 1` (`t ≤ q + 1` in `G_t_bounds`, which always holds by `s ≤ 1.94q`, `δ ≤ 10^{−3}`), so `q₀ = 1` works.
-/

namespace Collatz.M1

open Finset

/-! ## Basic properties of tails and swap blocks -/

/-- `τ ∈ 𝒯`: the first letter is 1, and there are `L − L_p` ones. -/
theorem G_mem_Tset {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) :
    (∀ h : 0 < s - P, τ ⟨0, h⟩ = true) ∧ ones τ (s - P) = L - Lp q := by
  unfold Tset at hτ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
  exact ⟨hτ.1, hτ.2.1⟩

/-- If `b ∈ ℬ(τ)`, then `b` is a swap block. -/
theorem G_mem_Bset {q s P : ℕ} {τ : Fin (s - P) → Bool} {b : ℕ} (hb : b ∈ Bset q s P τ) :
    IsSwap q s P τ b := by
  unfold Bset at hb
  simp only [Finset.mem_filter] at hb
  exact hb.2

/-- If there is a 1 among the first `j` letters of a word, then `o_j ≥ 1`. -/
theorem G_ones_pos {n : ℕ} (x : Fin n → Bool) (j p : ℕ) (hp : p < n) (hpj : p < j)
    (hx : x ⟨p, hp⟩ = true) : 1 ≤ ones x j := by
  unfold ones
  apply Finset.card_pos.mpr
  exact ⟨⟨p, hp⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hpj, hx⟩⟩

/-- If there is a 1 at a position `p ≥ j` with `p < j'`, then `o_j + 1 ≤ o_{j'}`. -/
theorem G_ones_succ_le {n : ℕ} (x : Fin n → Bool) (j j' p : ℕ) (hp : p < n) (hjp : j ≤ p)
    (hpj' : p < j') (hx : x ⟨p, hp⟩ = true) : ones x j + 1 ≤ ones x j' := by
  classical
  unfold ones
  have hnot : (⟨p, hp⟩ : Fin n) ∉ univ.filter (fun i : Fin n => (i : ℕ) < j ∧ x i = true) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; omega
  have hsub : insert (⟨p, hp⟩ : Fin n) (univ.filter (fun i : Fin n => (i : ℕ) < j ∧ x i = true)) ⊆
      univ.filter (fun i : Fin n => (i : ℕ) < j' ∧ x i = true) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with rfl | ⟨h1, h2⟩
    · exact ⟨hpj', hx⟩
    · exact ⟨by omega, h2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at this
  convert this using 2

/-- Properties of a swap block `b` of a tail in `𝒯`: `2b < t`, `b ≥ 1`, `L_p + 2 ≤ n_b ≤ L`, `d_b ≥ 2`. -/
theorem G_swap_facts {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) {b : ℕ}
    (hb : IsSwap q s P τ b) :
    2 * b < s - P ∧ 1 ≤ b ∧ Lp q + 2 ≤ nb q s P τ b ∧ nb q s P τ b ≤ L ∧ 2 ≤ db s P b ∧
      db s P b = (s - P) - (2 * b - 1) := by
  obtain ⟨h2b, hb1, hne, -⟩ := hb
  obtain ⟨h0, hones⟩ := G_mem_Tset hτ
  have hpos : 1 ≤ ones τ (2 * b - 1) :=
    G_ones_pos τ (2 * b - 1) 0 (by omega) (by omega) (h0 (by omega))
  -- position of the 1 in the block
  have hblk : ones τ (2 * b - 1) + 1 ≤ ones τ (s - P) := by
    by_cases h1 : τ ⟨2 * b - 1, by omega⟩ = true
    · exact G_ones_succ_le τ _ _ (2 * b - 1) (by omega) le_rfl (by omega) h1
    · have h2 : τ ⟨2 * b, h2b⟩ = true := by
        cases h3 : τ ⟨2 * b, h2b⟩
        · exfalso; apply hne; rw [h3]; simpa using h1
        · rfl
      exact G_ones_succ_le τ _ _ (2 * b) h2b (by omega) (by omega) h2
  refine ⟨h2b, hb1, ?_, ?_, ?_, rfl⟩
  · unfold nb jb; omega
  · unfold nb jb; omega
  · unfold db; omega


/-! ## Rotation within a fiber (step 1 of Lemma 9.1) -/

/-- Frequency of the swap block `b`: `α_b = ⟨2^{−d_b}⟩_{3^{n_b}}/3^{n_b}`. -/
noncomputable def alphaB (q s P : ℕ) (τ : Fin (s - P) → Bool) (b : ℕ) : ℝ :=
  (inv2mod (db s P b) (nb q s P τ b) 1 : ℝ) / 3 ^ nb q s P τ b

/-- `v_b = ⟨3^{−n_b}⟩_{2^{d_b}}`. -/
noncomputable def vB (q s P : ℕ) (τ : Fin (s - P) → Bool) (b : ℕ) : ℕ :=
  (((3 : ZMod (2 ^ db s P b)) ^ nb q s P τ b)⁻¹).val

/-- `cos² π(y − j) = cos² πy` (`j ∈ ℤ`). -/
theorem G_cos_sq_sub_int (y : ℝ) (j : ℤ) :
    Real.cos (Real.pi * (y - j)) ^ 2 = Real.cos (Real.pi * y) ^ 2 := by
  rw [Real.cos_sq, Real.cos_sq]
  congr 2
  rw [show 2 * (Real.pi * (y - j)) = 2 * (Real.pi * y) - j * (2 * Real.pi) by ring,
    Real.cos_sub_int_mul_two_pi]

/-- From Lemma 8.2 (i): at the point `N = 3^L ξ − 2^q κ` of the fiber `ξ`, `cos² πθ_b(N) = cos² π(κα_b)`. -/
theorem G_cos_theta {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) {b : ℕ}
    (hb : IsSwap q s P τ b) (ξ : ℕ) (hξ : ξ < 2 ^ q) (κ : ℤ) :
    Real.cos (Real.pi * theta q s P τ b (3 ^ L * (ξ : ℤ) - 2 ^ q * κ)) ^ 2 =
      Real.cos (Real.pi * (κ * alphaB q s P τ b)) ^ 2 := by
  obtain ⟨-, -, -, hn, -, -⟩ := G_swap_facts hτ hb
  rw [theta_kappa q s L P τ b _ hn, (xiN_kappaN_of q L ξ hξ κ).2]
  set n := nb q s P τ b
  set d := db s P b
  set w := ((κ : ZMod (3 ^ n)) * ((2 : ZMod (3 ^ n)) ^ d)⁻¹).val with hw
  set a := inv2mod d n 1 with ha
  obtain ⟨j, hj⟩ : ((3 ^ n : ℕ) : ℤ) ∣ κ * (a : ℤ) - w := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hw, ha, inv2mod, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Int.cast_one, one_mul]
  have hjR : (κ : ℝ) * a - w = 3 ^ n * j := by exact_mod_cast hj
  have : (w : ℝ) / 3 ^ n = κ * alphaB q s P τ b - j := by
    show (w : ℝ) / 3 ^ n = κ * ((a : ℝ) / 3 ^ n) - j
    field_simp
    linarith
  rw [this, G_cos_sq_sub_int]

/-- From Lemma 8.1: `α_b = 1 + 1/(2^{d_b}3^{n_b}) − v_b/2^{d_b}`. -/
theorem G_alpha_formula {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) {b : ℕ}
    (hb : IsSwap q s P τ b) :
    alphaB q s P τ b =
      1 + 1 / (2 ^ db s P b * 3 ^ nb q s P τ b) - (vB q s P τ b : ℝ) / 2 ^ db s P b := by
  obtain ⟨-, -, hn2, -, hd2, -⟩ := G_swap_facts hτ hb
  have hr := recip (db s P b) (nb q s P τ b) (by omega) (by omega)
  have hrR : (2 : ℝ) ^ db s P b * inv2mod (db s P b) (nb q s P τ b) 1 +
      3 ^ nb q s P τ b * vB q s P τ b = 1 + 2 ^ db s P b * 3 ^ nb q s P τ b := by
    unfold vB; exact_mod_cast hr
  unfold alphaB
  field_simp
  linear_combination hrR

/-- `v_b` is odd. -/
theorem G_vB_odd {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) {b : ℕ}
    (hb : IsSwap q s P τ b) : (vB q s P τ b : ℤ) % 2 = 1 := by
  obtain ⟨-, -, hn2, -, hd2, -⟩ := G_swap_facts hτ hb
  have hr := recip (db s P b) (nb q s P τ b) (by omega) (by omega)
  set d := db s P b
  set n := nb q s P τ b
  set a := inv2mod d n 1
  set v := vB q s P τ b
  change 2 ^ d * a + 3 ^ n * v = 1 + 2 ^ d * 3 ^ n at hr
  have hd : 2 ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hd] at hr
  have h1 : (3 ^ n * v) % 2 = 1 := by
    rw [mul_assoc, mul_assoc] at hr
    generalize 2 ^ (d - 1) * a = X at hr
    generalize 2 ^ (d - 1) * 3 ^ n = Z at hr
    generalize 3 ^ n * v = Y at hr ⊢
    omega
  have h3 : 3 ^ n % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [Nat.mul_mod, h3, one_mul, Nat.mod_mod] at h1
  omega


/-! ## Swap blocks in the window (steps 2 and 3 of Lemma 9.1) -/

/-- The swap blocks within distance `d` of the end: `B' = {b ∈ ℬ(τ) | d_b ≤ d}`. -/
noncomputable def Bwin (q s P : ℕ) (τ : Fin (s - P) → Bool) (d : ℕ) : Finset ℕ :=
  (Bset q s P τ).filter (fun b => db s P b ≤ d)

/-- `N_d(τ) = |B'|`. -/
theorem G_Nd_eq (q s P : ℕ) (τ : Fin (s - P) → Bool) (d : ℕ) : Nd q s P τ d = (Bwin q s P τ d).card := by
  unfold Nd Bwin; rfl

/-- If `b ∈ B'`, then `b` is a swap block and `d_b ≤ d`. -/
theorem G_mem_Bwin {q s P : ℕ} {τ : Fin (s - P) → Bool} {d b : ℕ} (hb : b ∈ Bwin q s P τ d) :
    IsSwap q s P τ b ∧ db s P b ≤ d := by
  unfold Bwin at hb
  rw [Finset.mem_filter] at hb
  exact ⟨G_mem_Bset hb.1, hb.2⟩

/-- `d_b` is injective on the window. -/
theorem G_db_injOn {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (d : ℕ) :
    Set.InjOn (db s P) (Bwin q s P τ d : Set ℕ) := by
  intro b hb b' hb' h
  obtain ⟨h2b, hb1, -, -, -, hdb⟩ := G_swap_facts hτ (G_mem_Bwin hb).1
  obtain ⟨h2b', hb1', -, -, -, hdb'⟩ := G_swap_facts hτ (G_mem_Bwin hb').1
  omega

/-- `Σ_b ε_b ≤ 2^{−d−1}` in step 3 of Lemma 9.1 (`ε_b = 1/(2^{d_b}3^{n_b})`, `d ≤ q + 1`). -/
theorem G_eps_sum {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (d : ℕ)
    (hdq : d ≤ q + 1) (hLp : 2 ^ q < 3 ^ (Lp q + 1)) :
    ∑ b ∈ Bwin q s P τ d, |1 / ((2 : ℝ) ^ db s P b * 3 ^ nb q s P τ b)| ≤ (1 / 2) ^ (d + 1) := by
  have hterm : ∀ b ∈ Bwin q s P τ d,
      |1 / ((2 : ℝ) ^ db s P b * 3 ^ nb q s P τ b)| ≤ (1 / 2) ^ db s P b * (1 / (3 * 2 ^ q)) := by
    intro b hb
    obtain ⟨-, -, hn2, -, -, -⟩ := G_swap_facts hτ (G_mem_Bwin hb).1
    rw [abs_of_pos (by positivity)]
    have h3 : (3 : ℝ) * 2 ^ q ≤ 3 ^ nb q s P τ b := by
      have : (2 : ℝ) ^ q < 3 ^ (Lp q + 1) := by exact_mod_cast hLp
      have h' : (3 : ℝ) ^ (Lp q + 2) ≤ 3 ^ nb q s P τ b := pow_le_pow_right₀ (by norm_num) hn2
      rw [pow_succ] at h'
      nlinarith
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    have : (0 : ℝ) < 2 ^ db s P b := by positivity
    nlinarith
  have hgeom : ∑ b ∈ Bwin q s P τ d, (1 / 2 : ℝ) ^ db s P b ≤ 1 / 2 := by
    rw [← Finset.sum_image (G_db_injOn hτ d)]
    calc ∑ j ∈ (Bwin q s P τ d).image (db s P), (1 / 2 : ℝ) ^ j
        ≤ ∑ j ∈ Finset.Ico 2 (d + 1), (1 / 2 : ℝ) ^ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            rw [Finset.mem_image] at hj
            obtain ⟨b, hb, rfl⟩ := hj
            obtain ⟨-, -, -, -, hd2, -⟩ := G_swap_facts hτ (G_mem_Bwin hb).1
            rw [Finset.mem_Ico]; exact ⟨hd2, by have := (G_mem_Bwin hb).2; omega⟩
          · intros; positivity
      _ ≤ (1 / 2) ^ 2 / (1 - 1 / 2) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ = 1 / 2 := by norm_num
  calc ∑ b ∈ Bwin q s P τ d, |1 / ((2 : ℝ) ^ db s P b * 3 ^ nb q s P τ b)|
      ≤ ∑ b ∈ Bwin q s P τ d, (1 / 2 : ℝ) ^ db s P b * (1 / (3 * 2 ^ q)) := Finset.sum_le_sum hterm
    _ = (∑ b ∈ Bwin q s P τ d, (1 / 2 : ℝ) ^ db s P b) * (1 / (3 * 2 ^ q)) := by
        rw [Finset.sum_mul]
    _ ≤ 1 / 2 * (1 / (3 * 2 ^ q)) := mul_le_mul_of_nonneg_right hgeom (by positivity)
    _ ≤ (1 / 2) ^ (d + 1) := by
        have h1 : (1 / 2 : ℝ) ^ (q + 2) ≤ (1 / 2) ^ (d + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have h2 : (1 / 2 : ℝ) ^ (q + 2) = 1 / (4 * 2 ^ q) := by
          rw [div_pow, one_pow, pow_add]; ring
        rw [h2] at h1
        have h3 : 1 / 2 * (1 / (3 * 2 ^ q)) ≤ 1 / (4 * (2 : ℝ) ^ q) := by
          rw [div_mul_div_comm, one_mul]
          apply one_div_le_one_div_of_le (by positivity)
          have : (0 : ℝ) < 2 ^ q := by positivity
          nlinarith
        linarith

/-- Step 3 of Lemma 9.1: for a pair `S ≠ S'` of subsets of the window, `α_S − α_{S'}` is at distance at least `2^{−d−1}` from the integers. -/
theorem G_alpha_sep {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (d : ℕ)
    (hdq : d ≤ q + 1) (hLp : 2 ^ q < 3 ^ (Lp q + 1)) :
    ∀ S ⊆ Bwin q s P τ d, ∀ S' ⊆ Bwin q s P τ d, S ≠ S' → ∀ m : ℤ,
      (1 / 2 : ℝ) ^ (d + 1) ≤ |∑ b ∈ S, alphaB q s P τ b - ∑ b ∈ S', alphaB q s P τ b - m| := by
  intro S hS S' hS' hne m
  have hsep := G_sep (Bwin q s P τ d) (db s P) (fun b => (vB q s P τ b : ℤ))
    (fun b => 1 / ((2 : ℝ) ^ db s P b * 3 ^ nb q s P τ b)) d
    (fun b hb => (G_swap_facts hτ (G_mem_Bwin hb).1).2.2.2.2.1)
    (fun b hb => (G_mem_Bwin hb).2) (G_db_injOn hτ d)
    (fun i hi j hj => by
      obtain ⟨h2b, hb1, -, -, -, hdb⟩ := G_swap_facts hτ (G_mem_Bwin hi).1
      obtain ⟨h2b', hb1', -, -, -, hdb'⟩ := G_swap_facts hτ (G_mem_Bwin hj).1
      omega)
    (fun b hb => G_vB_odd hτ (G_mem_Bwin hb).1)
    (G_eps_sum hτ d hdq hLp) S hS S' hS' hne m
  have e : ∀ T ⊆ Bwin q s P τ d, ∑ b ∈ T, alphaB q s P τ b =
      ∑ b ∈ T, (1 + 1 / ((2 : ℝ) ^ db s P b * 3 ^ nb q s P τ b) -
        (((vB q s P τ b : ℤ) : ℝ)) / 2 ^ db s P b) := by
    intro T hT
    apply Finset.sum_congr rfl; intro b hb
    rw [G_alpha_formula hτ (G_mem_Bwin (hT hb)).1]
    push_cast; ring
  rw [e S hS, e S' hS']
  exact hsep


/-! ## Average over an interval of a fiber (Lemma 9.1) -/

/-- The Riesz product is at most the product of the factors in the window alone (`cos² ≤ 1`). -/
theorem G_riesz_le_win (q s P : ℕ) (τ : Fin (s - P) → Bool) (d : ℕ) (N : ℤ) :
    riesz q s P τ N ≤ ∏ b ∈ Bwin q s P τ d, Real.cos (Real.pi * theta q s P τ b N) ^ 2 := by
  unfold riesz
  have hsub : Bwin q s P τ d ⊆ Bset q s P τ := Finset.filter_subset _ _
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ b ∈ Bset q s P τ \ Bwin q s P τ d, Real.cos (Real.pi * theta q s P τ b N) ^ 2 ≤ 1 := by
    apply cpt_prod_le_one
    · intro b _; positivity
    · intro b _; exact Real.cos_sq_le_one _
  have h2 : 0 ≤ ∏ b ∈ Bwin q s P τ d, Real.cos (Real.pi * theta q s P τ b N) ^ 2 := by
    apply Finset.prod_nonneg; intro b _; positivity
  calc _ ≤ 1 * ∏ b ∈ Bwin q s P τ d, Real.cos (Real.pi * theta q s P τ b N) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

/-- The Riesz product is nonnegative. -/
theorem G_riesz_nonneg (q s P : ℕ) (τ : Fin (s - P) → Bool) (N : ℤ) : 0 ≤ riesz q s P τ N := by
  unfold riesz; apply Finset.prod_nonneg; intro b _; positivity

/-- Steps 1–4 of Lemma 9.1 (one interval): `Σ_{x<U} Π_{b∈ℬ} cos² πθ_b(3^Lξ − 2^q(a+x)) ≤ U 2^{−N_d} + 2^d`. -/
theorem G_interval_bound {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (d : ℕ)
    (hdq : d ≤ q + 1) (hLp : 2 ^ q < 3 ^ (Lp q + 1)) (ξ : ℕ) (hξ : ξ < 2 ^ q) (a : ℤ) (U : ℕ) :
    ∑ x ∈ range U, riesz q s P τ (3 ^ L * (ξ : ℤ) - 2 ^ q * (a + x)) ≤
      U * (1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d := by
  calc ∑ x ∈ range U, riesz q s P τ (3 ^ L * (ξ : ℤ) - 2 ^ q * (a + x))
      ≤ ∑ x ∈ range U, ∏ b ∈ Bwin q s P τ d,
          Real.cos (Real.pi * theta q s P τ b (3 ^ L * (ξ : ℤ) - 2 ^ q * (a + x))) ^ 2 :=
        Finset.sum_le_sum (fun x _ => G_riesz_le_win q s P τ d _)
    _ = ∑ x ∈ range U, ∏ b ∈ Bwin q s P τ d,
          Real.cos (Real.pi * (a * alphaB q s P τ b + x * alphaB q s P τ b)) ^ 2 := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.prod_congr rfl; intro b hb
        rw [G_cos_theta hτ (G_mem_Bwin hb).1 ξ hξ]
        push_cast; ring_nf
    _ ≤ U * (1 / 2 : ℝ) ^ (Bwin q s P τ d).card + 1 / (2 * (1 / 2) ^ (d + 1)) :=
        G_riesz_sum (Bwin q s P τ d) (fun b => a * alphaB q s P τ b) (alphaB q s P τ) U
          ((1 / 2) ^ (d + 1)) (by positivity) (G_alpha_sep hτ d hdq hLp)
    _ = U * (1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d := by
        rw [G_Nd_eq]
        congr 1
        rw [pow_succ, div_pow, one_pow]; field_simp

/-- A sum over `Ico a (a + n)` is a sum over `range n`. -/
theorem G_sum_Ico_int (f : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    ∑ κ ∈ Ico a (a + n), f κ = ∑ x ∈ range n, f (a + x) := by
  apply Finset.sum_nbij' (fun κ => (κ - a).toNat) (fun x => a + x)
  · intro κ hκ
    simp only [Finset.mem_Ico, Finset.mem_range] at hκ ⊢
    omega
  · intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  · intro κ hκ
    simp only [Finset.mem_Ico] at hκ
    omega
  · intro x _
    simp
  · intro κ hκ
    simp only [Finset.mem_Ico] at hκ
    congr 1; omega

/-- Lemma 9.1 (one fiber): for `k ≥ 1`, `Σ_{κ∈I_k(ξ)} Π cos² πθ_b ≤ #I_k(ξ) (2^{−N_d} + 2^d 3^{−(k−1)})`. -/
theorem G_fiber_bound {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (d : ℕ)
    (hdq : d ≤ q + 1) (hLp : 2 ^ q < 3 ^ (Lp q + 1)) (k : ℕ) (hk : 1 ≤ k) (ξ : ℕ) (hξ : ξ < 2 ^ q) :
    ∑ κ ∈ Ik q L k ξ, riesz q s P τ (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) ≤
      (Ik q L k ξ).card * ((1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d / 3 ^ (k - 1)) := by
  have hcard := Ik_card q L k ξ
  rw [if_neg (by omega)] at hcard
  rw [hcard]
  unfold Ik
  rw [if_neg (by omega)]
  set f := fun κ : ℤ => riesz q s P τ (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) with hf
  have hU : ((3 : ℤ) ^ (k - 1)) = ((3 ^ (k - 1) : ℕ) : ℤ) := by push_cast; rfl
  set a1 := kappa0 q L ξ + mOne k + 1
  set a2 := kappa0 q L ξ + mTwo k + 1
  have hunion := Finset.sum_union_inter (s₁ := Ico a1 (a1 + 3 ^ (k - 1)))
    (s₂ := Ico a2 (a2 + 3 ^ (k - 1))) (f := f)
  have hinter : 0 ≤ ∑ κ ∈ Ico a1 (a1 + 3 ^ (k - 1)) ∩ Ico a2 (a2 + 3 ^ (k - 1)), f κ :=
    Finset.sum_nonneg (fun κ _ => G_riesz_nonneg q s P τ _)
  have hI : ∀ a : ℤ, ∑ κ ∈ Ico a (a + 3 ^ (k - 1)), f κ ≤
      (3 ^ (k - 1) : ℕ) * (1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d := by
    intro a
    rw [hU, G_sum_Ico_int]
    exact G_interval_bound hτ d hdq hLp ξ hξ a _
  have h1 := hI a1
  have h2 := hI a2
  have h3 : (0 : ℝ) < 3 ^ (k - 1) := by positivity
  calc ∑ κ ∈ Ico a1 (a1 + 3 ^ (k - 1)) ∪ Ico a2 (a2 + 3 ^ (k - 1)), f κ
      ≤ ∑ κ ∈ Ico a1 (a1 + 3 ^ (k - 1)), f κ + ∑ κ ∈ Ico a2 (a2 + 3 ^ (k - 1)), f κ := by linarith
    _ ≤ 2 * ((3 ^ (k - 1) : ℕ) * (1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d) := by linarith
    _ = ((2 * 3 ^ (k - 1) : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d / 3 ^ (k - 1)) := by
        push_cast; field_simp


/-- Lemma 9.1 (shell average, per tail): for `k ≥ 1`, `⟨Π_{b∈ℬ(τ)} cos² πθ_b⟩_k ≤ 2^{−N_d(τ)} + 2^d 3^{−(k−1)}`. -/
theorem G_shAvg_bound {q s L P : ℕ} {τ : Fin (s - P) → Bool} (hτ : τ ∈ Tset q s L P) (d : ℕ)
    (hdq : d ≤ q + 1) (hLp : 2 ^ q < 3 ^ (Lp q + 1)) (k : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    shAvg q s L k (riesz q s P τ) ≤ (1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d / 3 ^ (k - 1) := by
  unfold shAvg
  set Bd := (1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d / 3 ^ (k - 1) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hw0 : ∀ N, 0 ≤ wN q s L N := by
    intro N; unfold wN; split_ifs <;> positivity
  apply div_le_of_le_mul₀ (Finset.sum_nonneg (fun N _ => hw0 N)) hBd0
  rw [shell_fiber q L hq k (fun N => wN q s L N * riesz q s P τ N), shell_fiber q L hq k (wN q s L),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ξ hξ
  rw [Finset.mem_range] at hξ
  set Wξ := wN q s L (3 ^ L * (ξ : ℤ) - 2 ^ q * 0) with hWξ
  have hw : ∀ κ : ℤ, wN q s L (3 ^ L * (ξ : ℤ) - 2 ^ q * κ) = Wξ := by
    intro κ
    rw [hWξ]; unfold wN
    rw [(xiN_kappaN_of q L ξ hξ κ).1, (xiN_kappaN_of q L ξ hξ 0).1]
  simp_rw [hw]
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hfb := G_fiber_bound hτ d hdq hLp k hk ξ hξ
  have hW0 : 0 ≤ Wξ := hw0 _
  calc Wξ * ∑ κ ∈ Ik q L k ξ, riesz q s P τ (3 ^ L * (ξ : ℤ) - 2 ^ q * κ)
      ≤ Wξ * ((Ik q L k ξ).card * Bd) := mul_le_mul_of_nonneg_left hfb hW0
    _ = Bd * ((Ik q L k ξ).card * Wξ) := by ring

/-- Lemma 9.1: `A_k ≤ 𝔼_τ 2^{−N_d(τ)} + 2^d 3^{−(k−1)}` (`k ≥ 1`, `d ≤ q + 1`). -/
theorem G_Ak_bound {q s L P : ℕ} (hne : (Tset q s L P).Nonempty) (d : ℕ) (hdq : d ≤ q + 1)
    (hLp : 2 ^ q < 3 ^ (Lp q + 1)) (k : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    Ak q s L P k ≤ ETail q s L P d (fun n => (1 / 2 : ℝ) ^ n) + 2 ^ d / 3 ^ (k - 1) := by
  unfold Ak ETail
  have hT : (0 : ℝ) < (Tset q s L P).card := by exact_mod_cast hne.card_pos
  rw [div_add' _ _ _ hT.ne', div_le_div_iff_of_pos_right hT]
  calc ∑ τ ∈ Tset q s L P, shAvg q s L k (riesz q s P τ)
      ≤ ∑ τ ∈ Tset q s L P, ((1 / 2 : ℝ) ^ Nd q s P τ d + 2 ^ d / 3 ^ (k - 1)) :=
        Finset.sum_le_sum (fun τ hτ => G_shAvg_bound hτ d hdq hLp k hk hq)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring

/-! ## Proposition 9.2 -/

/-- `Y = (δ'q + 1 + 2 log₂ s)/log₂(1/Θ_*)` of Proposition 9.2. -/
noncomputable def Yout (δ' Θs : ℝ) (s q : ℕ) : ℝ :=
  (δ' * q + 1 + 2 * Real.logb 2 s) / Real.logb 2 (1 / Θs)

/-- `k₁ = 1 + ⌈(δ'q + 5 + 2Y)/λ⌉` of Proposition 9.2. -/
noncomputable def k1out (δ' Θs : ℝ) (s q : ℕ) : ℕ :=
  1 + ⌈(δ' * q + 5 + 2 * Yout δ' Θs s q) / lam⌉₊

/-! ## Auxiliary facts on the constants of Proposition 9.2 -/

/-- `λ > 0`. -/
theorem G_lam_pos : 0 < lam := by
  unfold lam; exact Real.logb_pos (by norm_num) (by norm_num)

/-- `λ < 2`. -/
theorem G_lam_lt_two : lam < 2 := by
  unfold lam
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
  norm_num

/-- `3^n = 2^{λn}`. -/
theorem G_pow3_eq (n : ℕ) : (3 : ℝ) ^ n = (2 : ℝ) ^ (lam * n) := by
  rw [Real.rpow_mul (by norm_num), ← G_three_eq_rpow, Real.rpow_natCast]

/-- `λ L_p ≤ q < λ(L_p + 1)`. -/
theorem G_lamLp (q : ℕ) : lam * Lp q ≤ q ∧ (q : ℝ) < lam * (Lp q + 1) := by
  obtain ⟨h1, h2⟩ := Lp_spec q
  constructor
  · have : (2 : ℝ) ^ (lam * Lp q) ≤ (2 : ℝ) ^ (q : ℝ) := by
      rw [← G_pow3_eq, Real.rpow_natCast]; exact_mod_cast h1
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mp this
  · have : (2 : ℝ) ^ (q : ℝ) < (2 : ℝ) ^ (lam * ((Lp q + 1 : ℕ) : ℝ)) := by
      rw [← G_pow3_eq, Real.rpow_natCast]; exact_mod_cast h2
    have := (Real.rpow_lt_rpow_left_iff (by norm_num)).mp this
    push_cast at this; exact this

/-- For a slice in `RdeltaG a b δ`: `P < q` and `t = s − P ≤ q + 1` (`s ≤ 1.94q`, `aδ ≤ 1.23×10^{−3}`). -/
theorem G_t_boundsG (a b δ : ℝ) (s q L P : ℕ) (haδ : a * δ ≤ 1.23e-3) (hs : (s : ℝ) ≤ 1.94 * q)
    (hR : RdeltaG a b δ s q L P) : P < q ∧ s - P ≤ q + 1 := by
  obtain ⟨-, -, hp0, hp1, -, -, hPs⟩ := hR
  obtain ⟨hl1, hl2⟩ := G_lamLp q
  have hlam2 := G_lam_lt_two
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hp1' : hp q P ≤ 1.23e-3 * q := hp1.trans (mul_le_mul_of_nonneg_right haδ hq0)
  unfold hp at hp0 hp1'
  have hPq : (P : ℝ) < q := by linarith
  constructor
  · exact_mod_cast hPq
  · have h : (s : ℝ) - P < q + 2 := by nlinarith
    have : ((s - P : ℕ) : ℝ) < q + 2 := by rw [Nat.cast_sub hPs.le]; exact h
    have : s - P < q + 2 := by exact_mod_cast this
    omega

-- The hypothesis `hδ` is not needed once the proof goes through the general form `G_t_boundsG` (the statement of the skeleton is kept).
set_option linter.unusedVariables false in
/-- For a slice in `R_δ`: `P < q` and `t = s − P ≤ q + 1` (`s ≤ 1.94q`, `δ ≤ 10^{−3}`). -/
theorem G_t_bounds (δ : ℝ) (s q L P : ℕ) (hδ1 : δ ≤ 1e-3) (hδ : 0 < δ) (hs : (s : ℝ) ≤ 1.94 * q)
    (hR : Rdelta δ s q L P) : P < q ∧ s - P ≤ q + 1 :=
  G_t_boundsG 1.23 3.5 δ s q L P (by linarith) hs hR

/-- `s² Θ_*^Y = 2^{−δ'q−1}`. -/
theorem G_first_term (δ' Θs : ℝ) (hΘ0 : 0 < Θs) (hΘ1 : Θs < 1) (s q : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) ^ 2 * Θs ^ Yout δ' Θs s q = (2 : ℝ) ^ (-(δ' * q) - 1) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hl : 0 < Real.logb 2 (1 / Θs) := Real.logb_pos (by norm_num) (by rw [lt_div_iff₀ hΘ0]; linarith)
  have hinv : Real.logb 2 (1 / Θs) = - Real.logb 2 Θs := by rw [one_div, Real.logb_inv]
  have hne : Real.logb 2 Θs ≠ 0 := by rw [hinv] at hl; linarith
  have hY : Real.logb 2 Θs * Yout δ' Θs s q = -(δ' * q + 1 + 2 * Real.logb 2 s) := by
    unfold Yout
    rw [hinv]
    field_simp
  have hpow : Θs ^ Yout δ' Θs s q = (2 : ℝ) ^ (Real.logb 2 Θs * Yout δ' Θs s q) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_logb (by norm_num) (by norm_num) hΘ0]
  have hs2 : (s : ℝ) ^ 2 = (2 : ℝ) ^ (2 * Real.logb 2 s) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hs0,
      Real.rpow_two]
  rw [hpow, hY, hs2, ← Real.rpow_add (by norm_num)]
  congr 1; ring

/-- `Θ_{1/2}(ρ) ≥ 0`. -/
theorem G_Theta_half_nonneg (ρ : ℝ) : 0 ≤ Theta (1 / 2) ρ := by
  unfold Theta; nlinarith [sq_nonneg (ρ - 1 / 2)]

/-- General form of Proposition 9.2 (`RdeltaG a b δ`, `aδ ≤ 1.23×10^{−3}`): if `0 < Θ_* < 1` satisfies `Θ_{1/2}(ρ̄) ≤ Θ_*` for every slice and
`⌊(s − q − 1)/2⌋ ≥ Y`, then, for `q` sufficiently large, `A_k ≤ 2^{−δ'q}` for every slice and every shell `k₁ ≤ k ≤ L`. -/
theorem outer_shellsG (a b δ δ' Θs : ℝ) (haδ : a * δ ≤ 1.23e-3) (hδ' : 0 < δ') (hΘ0 : 0 < Θs)
    (hΘ1 : Θs < 1) :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 →
      (∀ L P, RdeltaG a b δ s q L P → Theta (1 / 2) (rhoBar q s L P) ≤ Θs) →
      Yout δ' Θs s q ≤ ((s - q - 1) / 2 : ℕ) →
      ∀ L P, RdeltaG a b δ s q L P → ∀ k : ℕ, k1out δ' Θs s q ≤ k → k ≤ L →
        Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q)) := by
  refine ⟨1, ?_⟩
  intro s q hq hs1 hs2 hΘ hY L P hR k hk1 hkL
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : (q : ℝ) < s := by rwa [lt_div_iff₀ hqR, one_mul] at hs1
  have hs194 : (s : ℝ) ≤ 1.94 * q := by rwa [div_le_iff₀ hqR] at hs2
  have hs1' : 1 ≤ s := by
    have : (1 : ℝ) ≤ s := by linarith [show (1 : ℝ) ≤ q by exact_mod_cast hq]
    exact_mod_cast this
  obtain ⟨hL0, -, -, -, -, hne, hPs⟩ := id hR
  obtain ⟨hPq, htq⟩ := G_t_boundsG a b δ s q L P haδ hs194 hR
  have hLp := (Lp_spec q).2
  -- `Y > 0`
  have hlog : 0 < Real.logb 2 (1 / Θs) :=
    Real.logb_pos (by norm_num) (by rw [lt_div_iff₀ hΘ0]; linarith)
  have hlogs : 0 ≤ Real.logb 2 s := Real.logb_nonneg (by norm_num) (by exact_mod_cast hs1')
  have hYpos : 0 < Yout δ' Θs s q := by
    unfold Yout; apply div_pos _ hlog; positivity
  -- `s ≥ q + 3` from `⌊(s − q − 1)/2⌋ ≥ Y > 0`
  have hM1 : 1 ≤ (s - q - 1) / 2 := by
    have : (0 : ℝ) < ((s - q - 1) / 2 : ℕ) := lt_of_lt_of_le hYpos hY
    have : 0 < (s - q - 1) / 2 := by exact_mod_cast this
    omega
  have hs3 : q + 3 ≤ s := by omega
  -- `k ≥ 1`, `(k − 1)λ ≥ δ'q + 5 + 2Y`
  have hlam := G_lam_pos
  have hk1' : 1 ≤ k := by unfold k1out at hk1; omega
  have hkl : δ' * q + 5 + 2 * Yout δ' Θs s q ≤ ((k - 1 : ℕ) : ℝ) * lam := by
    have h1 : ⌈(δ' * q + 5 + 2 * Yout δ' Θs s q) / lam⌉₊ ≤ k - 1 := by unfold k1out at hk1; omega
    have h2 : (δ' * q + 5 + 2 * Yout δ' Θs s q) / lam ≤ ((k - 1 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rwa [div_le_iff₀ hlam] at h2
  -- `d' = ⌊(k−1)λ⌋ − ⌈δ'q⌉ − 1`
  set F := ⌊((k - 1 : ℕ) : ℝ) * lam⌋₊ with hF
  set C := ⌈δ' * q⌉₊ with hC
  have hF1 : ((k - 1 : ℕ) : ℝ) * lam < F + 1 := Nat.lt_floor_add_one _
  have hF2 : (F : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * lam := Nat.floor_le (by positivity)
  have hC1 : δ' * q ≤ C := Nat.le_ceil _
  have hC2 : (C : ℝ) < δ' * q + 1 := Nat.ceil_lt_add_one (by positivity)
  have hFC : C + 4 ≤ F := by
    have : (C : ℝ) + 3 < F := by linarith
    have : C + 3 < F := by exact_mod_cast this
    omega
  set d' := F - C - 1 with hd'
  have hd'R : (d' : ℝ) = F - C - 1 := by
    rw [hd', Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hd'Y : 2 * Yout δ' Θs s q + 2 < d' := by rw [hd'R]; linarith
  have hd'up : (d' : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * lam - δ' * q - 1 := by rw [hd'R]; linarith
  have hd'3 : 3 ≤ d' := by
    have : (2 : ℝ) < d' := by linarith
    have : 2 < d' := by exact_mod_cast this
    omega
  -- `d = min(t − 1, d')`
  set d := min (s - P - 1) d' with hd
  have hd2 : 2 ≤ d := by rw [hd]; apply le_min <;> omega
  have hdt : d ≤ s - P - 1 := min_le_left _ _
  have hdq : d ≤ q + 1 := by omega
  have hdd' : d ≤ d' := min_le_right _ _
  -- Lemma 9.1
  have hA := G_Ak_bound hne d hdq hLp k hk1' hq
  -- first term: Lemma 6.2
  have hW := window_count q s L P (1 / 2) (by norm_num) (by norm_num) d hd2 hdt hL0 hne
  have hΘP := hΘ L P hR
  have hΘn : 0 ≤ Theta (1 / 2) (rhoBar q s L P) := G_Theta_half_nonneg _
  have hnY : Yout δ' Θs s q ≤ (((d - 1) / 2 : ℕ) : ℝ) := by
    rcases le_total (s - P - 1) d' with h | h
    · have e : d = s - P - 1 := min_eq_left h
      rw [e]
      have : (s - q - 1) / 2 ≤ (s - P - 1 - 1) / 2 := Nat.div_le_div_right (by omega)
      calc Yout δ' Θs s q ≤ ((s - q - 1) / 2 : ℕ) := hY
        _ ≤ _ := by exact_mod_cast this
    · have e : d = d' := min_eq_right h
      rw [e]
      have h2 : d' - 2 ≤ 2 * ((d' - 1) / 2) := by omega
      have h3 : ((d' - 2 : ℕ) : ℝ) ≤ ((2 * ((d' - 1) / 2) : ℕ) : ℝ) := by exact_mod_cast h2
      rw [Nat.cast_sub (by omega)] at h3
      push_cast at h3
      linarith
  have hfirst : ETail q s L P d (fun n => (1 / 2 : ℝ) ^ n) ≤ (2 : ℝ) ^ (-(δ' * q) - 1) := by
    calc ETail q s L P d (fun n => (1 / 2 : ℝ) ^ n)
        ≤ ((s - P : ℕ) : ℝ) * ((s - P - 1 : ℕ) : ℝ) * Theta (1 / 2) (rhoBar q s L P) ^ ((d - 1) / 2) :=
          hW
      _ ≤ (s : ℝ) ^ 2 * Θs ^ ((d - 1) / 2) := by
          apply mul_le_mul _ (pow_le_pow_left₀ hΘn hΘP _) (by positivity) (by positivity)
          have h1 : ((s - P : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s P
          have h2 : ((s - P - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast (show s - P - 1 ≤ s by omega)
          have h3 : (0 : ℝ) ≤ ((s - P - 1 : ℕ) : ℝ) := by positivity
          nlinarith
      _ ≤ (s : ℝ) ^ 2 * Θs ^ Yout δ' Θs s q := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_ge hΘ0 hΘ1.le hnY
      _ = (2 : ℝ) ^ (-(δ' * q) - 1) := G_first_term δ' Θs hΘ0 hΘ1 s q hs1'
  -- second term
  have hsecond : (2 : ℝ) ^ d / 3 ^ (k - 1) ≤ (2 : ℝ) ^ (-(δ' * q) - 1) := by
    rw [div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ d ≤ 2 ^ d' := pow_le_pow_right₀ (by norm_num) hdd'
      _ = (2 : ℝ) ^ (d' : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) * lam - δ' * q - 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hd'up
      _ = (2 : ℝ) ^ (-(δ' * q) - 1) * 3 ^ (k - 1) := by
          rw [G_pow3_eq, ← Real.rpow_add (by norm_num)]; congr 1; ring
  have htot : (2 : ℝ) ^ (-(δ' * q) - 1) + 2 ^ (-(δ' * q) - 1) = 2 ^ (-(δ' * q)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]; ring
  linarith

-- The hypothesis `hδ` is not needed once the proof goes through the general form `outer_shellsG` (the statement of the skeleton is kept).
set_option linter.unusedVariables false in
/-- Proposition 9.2 (outer shells): if `0 < Θ_* < 1` satisfies `Θ_{1/2}(ρ̄) ≤ Θ_*` for every slice in `R_δ`
and `⌊(s − q − 1)/2⌋ ≥ Y`, then for `q` sufficiently large, `A_k ≤ 2^{−δ'q}` for every slice in `R_δ` and every shell `k₁ ≤ k ≤ L`. -/
theorem outer_shells (δ δ' Θs : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1e-3) (hδ' : 0 < δ') (hΘ0 : 0 < Θs)
    (hΘ1 : Θs < 1) :
    ∃ q0 : ℕ, ∀ s q : ℕ, q0 ≤ q → 1 < (s : ℝ) / q → (s : ℝ) / q ≤ 1.94 →
      (∀ L P, Rdelta δ s q L P → Theta (1 / 2) (rhoBar q s L P) ≤ Θs) →
      Yout δ' Θs s q ≤ ((s - q - 1) / 2 : ℕ) →
      ∀ L P, Rdelta δ s q L P → ∀ k : ℕ, k1out δ' Θs s q ≤ k → k ≤ L →
        Ak q s L P k ≤ (2:ℝ) ^ (-(δ' * q)) :=
  outer_shellsG 1.23 3.5 δ δ' Θs (by linarith) hδ' hΘ0 hΘ1

end Collatz.M1
