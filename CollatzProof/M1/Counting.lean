import CollatzProof.M1.Basics

/-!
# Counting for §2 (results used across sections)

Lemma 2.3 (general form of Chernoff), Lemma 2.5 (ii)(iii).

Proof tools (the name prefix `B_` marks auxiliary lemmas):
- Lemma 2.4 (rotation, `B_rotation`) and its word form `B_rot_surv`. The size of a cyclic-shift class is at most the length (`B_card_le_of_rot`).
- Lemma 2.3 is exponential tilting: the weight `2^{t*(y + λ|x| − q)}` of a surviving word is at least 1, and the sum of the weights is the letter-by-letter product
  `(2^{t*a} + 2^{−t*})^{q−j} = (2f)^{q−j}` (Lemma 1.7 (i)). Injectivity of `z ↦ u_q(z)` is `terras_inj`.
- The lower bound for the binomial coefficient in Lemma 2.5 (ii) (Lemma 2.1 (ii)) is shown from the mode inequality for the binomial distribution with `p = l/q`,
  `q^q ≤ (q+1) C(q,l) l^l (q−l)^{q−l}` (`B_mode`, an inequality of natural numbers), and Gibbs' inequality
  (`log x ≤ x − 1`) giving `H(ρ_c) ≤ H(l/q) + (l/q − ρ_c) log₂(p/(1−p))` (`B_entropy`).
-/

namespace Collatz.M1

open Finset

/-! ## Auxiliary: counting words (`B_` marks auxiliary lemmas for the counting lemmas of §2) -/

/-! ### Number of 1s in a word -/

/-- `ones` written as a sum. -/
theorem B_ones_eq_sum {n : ℕ} (x : Fin n → Bool) (j : ℕ) :
    ones x j = ∑ i : Fin n, (if (i : ℕ) < j ∧ x i = true then 1 else 0) := by
  unfold ones; rw [card_filter]

/-- `o_j(x) ≤ n`. -/
theorem B_ones_le {n : ℕ} (x : Fin n → Bool) (j : ℕ) : ones x j ≤ n := by
  unfold ones
  calc _ ≤ (univ : Finset (Fin n)).card := card_filter_le _ _
    _ = n := by simp

/-- When a word is represented as a sequence on `ℕ`, `ones` for `j ≤ n` is a sum over a range. -/
theorem B_ones_eq_range {n : ℕ} (x : Fin n → Bool) (X : ℕ → Bool)
    (hX : ∀ i : Fin n, X i = x i) (j : ℕ) (hj : j ≤ n) :
    ones x j = ∑ i ∈ range j, (if X i = true then 1 else 0) := by
  rw [B_ones_eq_sum]
  have : ∀ i : Fin n, (if (i : ℕ) < j ∧ x i = true then 1 else 0) =
      (fun k : ℕ => if k < j then (if X k = true then 1 else 0) else 0) (i : ℕ) := by
    intro i; simp only [hX, ite_and]
  rw [Finset.sum_congr rfl (fun i _ => this i),
    Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < j then (if X k = true then 1 else 0) else 0) n,
    ← Finset.sum_filter]
  have hr : (range n).filter (fun k => k < j) = range j := by
    ext k; simp only [mem_filter, mem_range]; constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨lt_of_lt_of_le h hj, h⟩
  rw [hr]

/-! ### Lemma 2.4 (rotation) -/

/-- Cyclic shift of a word: `(rot x r) i = x ((r + i) mod n)`. -/
def B_rot {n : ℕ} (x : Fin n → Bool) (r : ℕ) : Fin n → Bool :=
  fun i => x ⟨(r + i) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Periodic extension of a word. -/
def B_per {n : ℕ} (x : Fin n → Bool) (hn : 0 < n) : ℕ → Bool :=
  fun i => x ⟨i % n, Nat.mod_lt _ hn⟩

/-- Inverse of the cyclic shift: if `r ≤ n` then `rot (rot x r) (n − r) = x`. -/
theorem B_rot_rot {n : ℕ} (x : Fin n → Bool) (r : ℕ) (hr : r ≤ n) :
    B_rot (B_rot x r) (n - r) = x := by
  funext i
  simp only [B_rot]
  congr 1
  ext
  simp only
  rw [Nat.add_mod_mod, show r + (n - r + (i:ℕ)) = n + i by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt i.isLt]

/-- The number of 1s of a shifted word is a sum over an interval of the periodic extension. -/
theorem B_ones_rot {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (r j : ℕ) (hj : j ≤ n) :
    ones (B_rot x r) j = ∑ i ∈ range j, (if B_per x hn (r + i) = true then 1 else 0) :=
  B_ones_eq_range (B_rot x r) (fun i => B_per x hn (r + i)) (fun _ => rfl) j hj

/-- Shift by 0 is the identity. -/
theorem B_rot_zero {n : ℕ} (x : Fin n → Bool) : B_rot x 0 = x := by
  funext i; simp only [B_rot, zero_add, Nat.mod_eq_of_lt i.isLt]

/-- Lemma 2.4 (rotation): for the partial sums `Σ` of an `n`-periodic real sequence, the partial sums starting from some `r < n`
are all at least `min(0, Σ(n))`. -/
theorem B_rotation (g : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hper : ∀ i, g (n + i) = g i) :
    ∃ r < n, ∀ m ≤ n,
      min 0 (∑ i ∈ range n, g i) ≤ ∑ i ∈ range (r + m), g i - ∑ i ∈ range r, g i := by
  set Sg : ℕ → ℝ := fun m => ∑ i ∈ range m, g i with hSg
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (range n) Sg (nonempty_range_iff.mpr hn.ne')
  rw [mem_range] at hr
  refine ⟨r, hr, fun m hm => ?_⟩
  have h0 : Sg r ≤ 0 := by
    have := hmin 0 (mem_range.mpr hn); simpa [hSg] using this
  by_cases hlt : r + m < n
  · have := hmin (r + m) (mem_range.mpr hlt)
    have : (0:ℝ) ≤ Sg (r + m) - Sg r := by linarith
    exact le_trans (min_le_left _ _) this
  · obtain ⟨m', hm'⟩ : ∃ m', r + m = n + m' := ⟨r + m - n, by omega⟩
    have hm'n : m' < n := by omega
    have hsplit : Sg (n + m') = Sg n + Sg m' := by
      simp only [hSg, Finset.sum_range_add, hper]
    have := hmin m' (mem_range.mpr hm'n)
    change min 0 (Sg n) ≤ Sg (r + m) - Sg r
    rw [hm', hsplit]
    have : Sg n ≤ Sg n + Sg m' - Sg r := by linarith
    exact le_trans (min_le_right _ _) this

/-- The increment sequence: `λ − 1` for `1`, `−1` for `0`. -/
noncomputable def B_inc {n : ℕ} (x : Fin n → Bool) (hn : 0 < n) : ℕ → ℝ :=
  fun i => if B_per x hn i = true then lam - 1 else -1

/-- The increment sequence has period `n`. -/
theorem B_inc_per {n : ℕ} (x : Fin n → Bool) (hn : 0 < n) (i : ℕ) :
    B_inc x hn (n + i) = B_inc x hn i := by
  have h : (⟨(n + i) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i % n, Nat.mod_lt _ hn⟩ :=
    Fin.ext (Nat.add_mod_left n i)
  simp only [B_inc, B_per, h]
  rfl

/-- The height increment `λ o_j − j` of a shifted word is a sum over an interval of the increment sequence. -/
theorem B_height_rot {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (r j : ℕ) (hj : j ≤ n) :
    lam * (ones (B_rot x r) j : ℝ) - j = ∑ i ∈ range j, B_inc x hn (r + i) := by
  rw [B_ones_rot hn x r j hj]
  push_cast
  rw [Finset.mul_sum]
  have : (j : ℝ) = ∑ i ∈ range j, (1:ℝ) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [B_inc]
  split_ifs <;> ring

/-- Survival by rotation (word form of Lemma 2.4): if `y ≥ 0` and the final height `y + λ|x| − n ≥ 0`,
then some cyclic shift survives from height `y`. -/
theorem B_rot_surv {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (y : ℝ) (hy : 0 ≤ y)
    (hS : 0 ≤ y + lam * ones x n - n) : ∃ r < n, SurvW y (B_rot x r) := by
  obtain ⟨r, hr, hmin⟩ := B_rotation (B_inc x hn) n hn (B_inc_per x hn)
  refine ⟨r, hr, fun j _ hj => ?_⟩
  have hS' : ∑ i ∈ range n, B_inc x hn i = lam * (ones x n : ℝ) - n := by
    have := B_height_rot hn x 0 n le_rfl
    simp only [B_rot_zero, zero_add] at this
    exact this.symm
  have hj' := hmin j hj
  rw [hS', Finset.sum_range_add, add_sub_cancel_left, ← B_height_rot hn x r j hj] at hj'
  simp only [hw]
  have : min 0 (lam * (ones x n : ℝ) - n) + y ≥ 0 := by
    rcases le_total 0 (lam * (ones x n : ℝ) - n) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  linarith

/-! ### Weight computation for Lemma 2.3 -/

/-- `ones` over the full length is the number of letters equal to 1. -/
theorem B_ones_full {m : ℕ} (x : Fin m → Bool) :
    ones x m = (univ.filter (fun i => x i = true)).card := by
  unfold ones
  congr 1
  ext i; simp

/-- Letter-by-letter product `∏ (x_i ? A : B) = A^{|x|} B^{n−|x|}`. -/
theorem B_prod_ite {m : ℕ} (x : Fin m → Bool) (A B : ℝ) :
    ∏ i, (if x i = true then A else B) = A ^ (ones x m) * B ^ (m - ones x m) := by
  rw [prod_ite, prod_const, prod_const, B_ones_full]
  congr 2
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun i => x i = true)
  simp only [card_univ, Fintype.card_fin] at this
  omega

/-- The set of words of length `q` whose first `j` letters are fixed to `w₁`. -/
def B_pre (q j : ℕ) (w₁ : Fin j → Bool) : Finset (Fin q → Bool) :=
  Fintype.piFinset (fun i : Fin q => if h : (i : ℕ) < j then {w₁ ⟨i, h⟩} else univ)

/-- The elements of `B_pre` are the words whose first `j` letters are `w₁`. -/
theorem B_mem_pre {q j : ℕ} (w₁ : Fin j → Bool) (x : Fin q → Bool) (hj : j ≤ q) :
    x ∈ B_pre q j w₁ ↔ ∀ i : Fin j, x ⟨i, by omega⟩ = w₁ i := by
  unfold B_pre
  rw [Fintype.mem_piFinset]
  constructor
  · intro h i
    have := h ⟨i, by omega⟩
    simp only [i.isLt, ↓reduceDIte, mem_singleton] at this
    exact this
  · intro h i
    by_cases hi : (i : ℕ) < j
    · simp only [hi, ↓reduceDIte, mem_singleton]
      exact h ⟨i, hi⟩
    · simp [hi]

/-- Sum of the letter-by-letter product over the words with the first `j` letters fixed: `∏_{i<j} g(w₁ i) · (A + B)^{q−j}`. -/
theorem B_sum_pre (q j : ℕ) (hj : j ≤ q) (w₁ : Fin j → Bool) (A B : ℝ) :
    ∑ x ∈ B_pre q j w₁, ∏ i, (if x i = true then A else B) =
      (∏ i : Fin j, (if w₁ i = true then A else B)) * (A + B) ^ (q - j) := by
  unfold B_pre
  rw [← prod_univ_sum (κ := fun _ => Bool)
    (fun i : Fin q => if h : (i : ℕ) < j then {w₁ ⟨i, h⟩} else univ)
    (fun _ b => if b = true then A else B)]
  set G : ℕ → ℝ := fun k => if h : k < j then (if w₁ ⟨k, h⟩ = true then A else B) else A + B with hG
  have h1 : ∀ i : Fin q, ∑ b ∈ (if h : (i : ℕ) < j then {w₁ ⟨i, h⟩} else univ),
      (if b = true then A else B) = G i := by
    intro i
    by_cases hi : (i : ℕ) < j
    · simp [hG, hi]
    · simp [hG, hi]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Fin.prod_univ_eq_prod_range G q]
  obtain ⟨d, rfl⟩ : ∃ d, q = j + d := ⟨q - j, by omega⟩
  rw [prod_range_add, ← Fin.prod_univ_eq_prod_range G j]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [hG, i.isLt]
  · rw [show j + d - j = d by omega]
    rw [Finset.prod_congr rfl (fun k _ => show G (j + k) = A + B by simp [hG]), prod_const,
      card_range]

/-- `o_0(x) = 0`. -/
theorem B_ones_zero {n : ℕ} (x : Fin n → Bool) : ones x 0 = 0 := by
  unfold ones; simp

/-- The final height of a surviving word is at least 0 (for `n = 0` we use `y ≥ 0`). -/
theorem B_final_height {n : ℕ} (x : Fin n → Bool) (y : ℝ) (hy : 0 ≤ y) (hs : SurvW y x) :
    0 ≤ hw y x n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [hw, B_ones_zero, hy]
  · exact hs n h le_rfl

/-- Injectivity of Terras (in the `pw` form). -/
theorem B_pw_inj {q z z' : ℕ} (hz : z < 2 ^ q) (hz' : z' < 2 ^ q) (h : pw z q = pw z' q) :
    z = z' := by
  apply terras_inj q z z' hz hz'
  intro i hi
  have := congrFun h ⟨i, hi⟩
  simp only [pw] at this
  have h1 := Nat.mod_two_eq_zero_or_one (T^[i] z)
  have h2 := Nat.mod_two_eq_zero_or_one (T^[i] z')
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/-- Characterization of the elements of `E`. -/
theorem B_mem_Eset {q : ℕ} {y : ℝ} {z : ℕ} : z ∈ Eset q y ↔ z < 2 ^ q ∧ SurvW y (pw z q) := by
  unfold Eset; simp

/-- The weight `2^{t* y} A^{|x|} B^{q−|x|}` is at least 1 on surviving words. -/
theorem B_weight_ge_one {q : ℕ} (x : Fin q → Bool) (y : ℝ) (hy : 0 ≤ y) (hs : SurvW y x) :
    (1:ℝ) ≤ (2:ℝ) ^ (tstar * y) *
      ∏ i, (if x i = true then (2:ℝ) ^ (tstar * aa) else (2:ℝ) ^ (-tstar)) := by
  have ht : 0 < tstar := by linarith [tstar_bounds.1]
  rw [B_prod_ite, ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_mul_natCast (by norm_num),
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  apply Real.one_le_rpow (by norm_num)
  have hf := B_final_height x y hy hs
  have hle := B_ones_le x q
  simp only [hw] at hf
  rw [Nat.cast_sub hle]
  have : tstar * y + (tstar * aa * (ones x q : ℝ) + -tstar * ((q : ℝ) - ones x q)) =
      tstar * (y + lam * ones x q - q) := by simp only [aa]; ring
  rw [this]
  exact mul_nonneg ht.le hf

/-! ### Counting for Lemma 2.5 (cyclic-shift classes) -/

/-- Counting cyclic-shift classes: if every element of `D` can be written as `F b r` for some `r < n` and `b ∈ B`, then `|D| ≤ |B| n`. -/
theorem B_card_le_of_rot {n : ℕ} {β : Type*} [DecidableEq β] (D : Finset (Fin n → Bool))
    (B : Finset β) (F : β → ℕ → (Fin n → Bool)) (h : ∀ x ∈ D, ∃ r < n, ∃ b ∈ B, F b r = x) :
    D.card ≤ B.card * n := by
  classical
  have hsub : D ⊆ (B ×ˢ range n).image (fun p => F p.1 p.2) := by
    intro x hx
    obtain ⟨r, hr, b, hb, rfl⟩ := h x hx
    rw [mem_image]
    exact ⟨(b, r), mem_product.mpr ⟨hb, mem_range.mpr hr⟩, rfl⟩
  calc D.card ≤ ((B ×ˢ range n).image (fun p => F p.1 p.2)).card := card_le_card hsub
    _ ≤ (B ×ˢ range n).card := card_image_le
    _ = B.card * n := by rw [card_product, card_range]

/-- There are at least `C(n, k)` words of length `n` with `k` ones. -/
theorem B_choose_le_words (n k : ℕ) :
    n.choose k ≤ (univ.filter (fun x : Fin n → Bool => ones x n = k)).card := by
  classical
  have h1 : (powersetCard k (univ : Finset (Fin n))).card = n.choose k := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [← h1]
  apply card_le_card_of_injOn (fun A => fun i => decide (i ∈ A))
  · intro A hA
    rw [mem_coe, mem_powersetCard] at hA
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [B_ones_full]
    simp only [decide_eq_true_eq, filter_mem_eq_inter, univ_inter]
    exact hA.2
  · intro A _ A' _ h
    ext i
    have := congrFun h i
    simpa using this

/-- The sum over one period of a periodic sequence does not depend on the starting point. -/
theorem B_sum_shift (g : ℕ → ℝ) (n : ℕ) (hper : ∀ i, g (n + i) = g i) (r : ℕ) :
    ∑ i ∈ range n, g (r + i) = ∑ i ∈ range n, g i := by
  have h1 := sum_range_add g r n
  have h2 := sum_range_add g n r
  simp only [hper] at h2
  rw [add_comm r n] at h1
  linarith

/-- A cyclic shift preserves the number of 1s. -/
theorem B_ones_rot_full {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (r : ℕ) :
    ones (B_rot x r) n = ones x n := by
  have h := B_ones_rot hn x r n le_rfl
  have h0 := B_ones_rot hn x 0 n le_rfl
  rw [B_rot_zero] at h0
  have key : ((ones (B_rot x r) n : ℕ) : ℝ) = ((ones x n : ℕ) : ℝ) := by
    rw [h, h0]; push_cast
    simp only [zero_add]
    apply B_sum_shift (fun i => if B_per x hn i = true then (1:ℝ) else 0) n
    intro i
    have e : (⟨(n + i) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i % n, Nat.mod_lt _ hn⟩ :=
      Fin.ext (Nat.add_mod_left n i)
    simp only [B_per, e]
    rfl
  exact_mod_cast key

/-- The number of 1s of a word with a letter prepended. -/
theorem B_ones_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) (j : ℕ) :
    ones (Fin.cons b w : Fin (n + 1) → Bool) (j + 1) = (if b = true then 1 else 0) + ones w j := by
  rw [B_ones_eq_sum, B_ones_eq_sum, Fin.sum_univ_succ]
  simp

/-- Survival of a word with 1 prepended: if `w` survives from height `y + a` and `y + a ≥ 0`, then `1w` survives from height `y`. -/
theorem B_surv_cons {n : ℕ} (w : Fin n → Bool) (y : ℝ) (hy : 0 ≤ y + aa) (hs : SurvW (y + aa) w) :
    SurvW y (Fin.cons true w : Fin (n + 1) → Bool) := by
  intro j hj1 hj2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [hw, B_ones_cons]
  push_cast
  rcases Nat.eq_zero_or_pos j' with h | h
  · subst h; simp only [B_ones_zero, Nat.cast_zero, aa] at hy ⊢; linarith
  · have := hs j' h (by omega)
    simp only [hw, aa] at this hy
    linarith

/-- The core of Lemma 2.5 (iii) (for a set `T'` of words of length `t = n + 1`). -/
theorem B_T_aux (t n k : ℕ) (htn : t = n + 1) (hn : 0 < n) (y : ℝ) (hy : 0 ≤ y + aa)
    (hend : 0 ≤ y + aa + lam * k - n) (T' : Finset (Fin t → Bool))
    (hT' : ∀ τ : Fin t → Bool, (∀ h : 0 < t, τ ⟨0, h⟩ = true) → ones τ t = k + 1 → SurvW y τ →
      τ ∈ T') :
    (n.choose k : ℝ) / n ≤ T'.card := by
  classical
  subst htn
  set Dw := univ.filter (fun x : Fin n → Bool => ones x n = k) with hDw
  have hmain : Dw.card ≤ T'.card * n := by
    apply B_card_le_of_rot Dw T' (fun τ r => B_rot (Fin.tail τ) (n - r))
    intro w hw'
    rw [hDw, mem_filter] at hw'
    have hk := hw'.2
    obtain ⟨r, hr, hsurv⟩ := B_rot_surv hn w (y + aa) hy (by rw [hk]; linarith)
    refine ⟨r, hr, Fin.cons true (B_rot w r), ?_, ?_⟩
    · apply hT'
      · intro _; rfl
      · rw [B_ones_cons, B_ones_rot_full hn, hk]; simp [add_comm]
      · exact B_surv_cons _ y hy hsurv
    · simp only [Fin.tail_cons]
      exact B_rot_rot w r hr.le
  have h1 := B_choose_le_words n k
  have h2 : (n.choose k : ℝ) ≤ T'.card * n := by exact_mod_cast le_trans h1 hmain
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  exact h2

/-- Characterization of the elements of `𝒯_{L,P}`. -/
theorem B_mem_Tset {q s L P : ℕ} (τ : Fin (s - P) → Bool) :
    τ ∈ Tset q s L P ↔ (∀ h : 0 < s - P, τ ⟨0, h⟩ = true) ∧ ones τ (s - P) = L - Lp q ∧
      SurvW (hp q P) τ := by
  unfold Tset; simp

/-! ### Analytic part of Lemma 2.1 (ii) and Lemma 2.5 (ii) -/

/-- Terms of the binomial distribution (with `p = l/q`, multiplied by `q^q`): `U_i = C(q,i) l^i (q−l)^{q−i}`. -/
def B_U (q l i : ℕ) : ℕ := q.choose i * l ^ i * (q - l) ^ (q - i)

/-- Ratio of adjacent terms: `U_{i+1} (i+1)(q−l) = U_i (q−i) l`. -/
theorem B_U_succ (q l i : ℕ) (hi : i < q) :
    B_U q l (i + 1) * ((i + 1) * (q - l)) = B_U q l i * ((q - i) * l) := by
  have hc := Nat.choose_succ_right_eq q i
  have hp : (q - l) ^ (q - i) = (q - l) ^ (q - (i + 1)) * (q - l) := by
    rw [← pow_succ]; congr 1; omega
  unfold B_U
  rw [hp]
  calc q.choose (i + 1) * l ^ (i + 1) * (q - l) ^ (q - (i + 1)) * ((i + 1) * (q - l))
      = (q.choose (i + 1) * (i + 1)) * l ^ (i + 1) * ((q - l) ^ (q - (i + 1)) * (q - l)) := by ring
    _ = (q.choose i * (q - i)) * l ^ (i + 1) * ((q - l) ^ (q - (i + 1)) * (q - l)) := by rw [hc]
    _ = q.choose i * l ^ i * ((q - l) ^ (q - (i + 1)) * (q - l)) * ((q - i) * l) := by ring

/-- For `i < l`, `U_i ≤ U_{i+1}`. -/
theorem B_U_inc (q l i : ℕ) (hl : l < q) (hi : i < l) : B_U q l i ≤ B_U q l (i + 1) := by
  have hrec := B_U_succ q l i (by omega)
  have hc : 0 < (i + 1) * (q - l) := Nat.mul_pos (by omega) (by omega)
  have hd : (i + 1) * (q - l) ≤ (q - i) * l := by
    obtain ⟨a, rfl⟩ : ∃ a, l = i + 1 + a := ⟨l - (i + 1), by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = i + 1 + a + b + 1 := ⟨q - (i + 1 + a) - 1, by omega⟩
    rw [show i + 1 + a + b + 1 - (i + 1 + a) = b + 1 by omega,
      show i + 1 + a + b + 1 - i = a + b + 2 by omega]
    nlinarith
  apply Nat.le_of_mul_le_mul_right _ hc
  rw [hrec]
  exact Nat.mul_le_mul_left _ hd

/-- For `l ≤ i < q`, `U_{i+1} ≤ U_i`. -/
theorem B_U_dec (q l i : ℕ) (hl : l < q) (hi : l ≤ i) (hiq : i < q) :
    B_U q l (i + 1) ≤ B_U q l i := by
  have hrec := B_U_succ q l i hiq
  have hc : 0 < (i + 1) * (q - l) := Nat.mul_pos (by omega) (by omega)
  have hd : (q - i) * l ≤ (i + 1) * (q - l) := by
    obtain ⟨a, rfl⟩ : ∃ a, i = l + a := ⟨i - l, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = l + a + b + 1 := ⟨q - (l + a) - 1, by omega⟩
    rw [show l + a + b + 1 - (l + a) = b + 1 by omega,
      show l + a + b + 1 - l = a + b + 1 by omega]
    nlinarith
  apply Nat.le_of_mul_le_mul_right _ hc
  rw [hrec]
  exact Nat.mul_le_mul_left _ hd

/-- Mode: `U_i ≤ U_l` for all `i ≤ q`. -/
theorem B_U_le (q l i : ℕ) (hl : l < q) (hi : i ≤ q) : B_U q l i ≤ B_U q l l := by
  rcases le_total i l with h | h
  · have key : ∀ d, ∀ i, i + d = l → B_U q l i ≤ B_U q l l := by
      intro d
      induction d with
      | zero => intro i h; simp at h; rw [h]
      | succ d ih =>
        intro i h
        exact le_trans (B_U_inc q l i hl (by omega)) (ih (i + 1) (by omega))
    exact key (l - i) i (by omega)
  · have key : ∀ d, l + d ≤ q → B_U q l (l + d) ≤ B_U q l l := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro h
        exact le_trans (B_U_dec q l (l + d) hl (by omega) (by omega)) (ih (by omega))
    have := key (i - l) (by omega)
    rwa [show l + (i - l) = i by omega] at this

/-- Mode inequality (in the form of Lemma 2.1 (ii)): if `l < q` then `q^q ≤ (q+1) C(q,l) l^l (q−l)^{q−l}`. -/
theorem B_mode (q l : ℕ) (hl : l < q) : q ^ q ≤ (q + 1) * B_U q l l := by
  have h1 : q ^ q = ∑ m ∈ range (q + 1), B_U q l m := by
    have := add_pow (l : ℕ) (q - l) q
    rw [show l + (q - l) = q by omega] at this
    rw [this]
    apply sum_congr rfl
    intro m _
    unfold B_U; rw [Nat.cast_id]; ring
  rw [h1]
  calc ∑ m ∈ range (q + 1), B_U q l m ≤ ∑ m ∈ range (q + 1), B_U q l l := by
        apply sum_le_sum
        intro m hm
        exact B_U_le q l m hl (by rw [mem_range] at hm; omega)
    _ = (q + 1) * B_U q l l := by rw [sum_const, card_range, smul_eq_mul]

/-- `(1 − c) ln 2 = −ρ_c ln ρ_c − (1 − ρ_c) ln(1 − ρ_c)`. -/
theorem B_one_sub_cc_log :
    (1 - cc) * Real.log 2 = -(rhoc * Real.log rhoc) - (1 - rhoc) * Real.log (1 - rhoc) := by
  have h2 : Real.log 2 ≠ 0 := by positivity
  simp only [cc, Hb, Real.logb]
  field_simp
  ring

/-- Analytic part of Lemma 2.5 (ii): if `q ≥ 20` and `qρ_c < l ≤ qρ_c + 1` then
`2^{(1−c)q − 1.1} l^l (q−l)^{q−l} ≤ q^q`. -/
theorem B_entropy (q l : ℕ) (hq : 20 ≤ q) (hl1 : (q:ℝ) * rhoc < l) (hl2 : (l:ℝ) ≤ q * rhoc + 1)
    (hlq : l < q) :
    (2:ℝ) ^ ((1 - cc) * q - 1.1) * ((l:ℝ) ^ l * ((q - l : ℕ) : ℝ) ^ (q - l)) ≤ (q:ℝ) ^ q := by
  obtain ⟨hρ1, hρ2⟩ := rhoc_bounds
  set ρ := rhoc with hρ
  have hq' : (20:ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0:ℝ) < q := by linarith
  have hlpos : (0:ℝ) < l := by nlinarith
  have hql : ((q - l : ℕ) : ℝ) = q - l := Nat.cast_sub hlq.le
  have hlq' : (l:ℝ) < q := by exact_mod_cast hlq
  have hqlpos : (0:ℝ) < q - l := by linarith
  rw [hql]
  have hL : 0 < (2:ℝ) ^ ((1 - cc) * q - 1.1) * ((l:ℝ) ^ l * ((q:ℝ) - l) ^ (q - l)) := by
    positivity
  rw [← Real.log_le_log_iff hL (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num), Real.log_pow,
    Real.log_pow, Real.log_pow, Nat.cast_sub hlq.le]
  -- Gibbs' inequality (`log x ≤ x − 1`)
  have g1 := Real.log_le_sub_one_of_pos (show 0 < (l:ℝ) / (q * ρ) by positivity)
  have g2 := Real.log_le_sub_one_of_pos (show 0 < ((q:ℝ) - l) / (q * (1 - ρ)) by
    apply div_pos hqlpos; apply mul_pos hqpos; linarith)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    at g1
  rw [Real.log_div (by positivity) (by nlinarith), Real.log_mul (by positivity) (by linarith)]
    at g2
  have F1 : q * ρ * (Real.log l - (Real.log q + Real.log ρ)) ≤ l - q * ρ := by
    have hqρ : 0 < (q:ℝ) * ρ := by positivity
    have := mul_le_mul_of_nonneg_left g1 hqρ.le
    have e : (q:ℝ) * ρ * ((l:ℝ) / (q * ρ) - 1) = l - q * ρ := by field_simp
    rw [e] at this
    exact this
  have F2 : q * (1 - ρ) * (Real.log (q - l) - (Real.log q + Real.log (1 - ρ))) ≤
      (q - l) - q * (1 - ρ) := by
    have hqρ : 0 < (q:ℝ) * (1 - ρ) := by apply mul_pos hqpos; linarith
    have := mul_le_mul_of_nonneg_left g2 hqρ.le
    have hne : (1:ℝ) - ρ ≠ 0 := (show (0:ℝ) < 1 - ρ by linarith).ne'
    have e : (q:ℝ) * (1 - ρ) * (((q:ℝ) - l) / (q * (1 - ρ)) - 1) = (q - l) - q * (1 - ρ) := by
      field_simp
    rw [e] at this
    exact this
  have F3 := B_one_sub_cc_log
  rw [← hρ] at F3
  -- `X = log l − log(q − l) ∈ [0, 1.1 log 2]`
  have hX0 : 0 ≤ Real.log l - Real.log (q - l) := by
    have : Real.log (q - l) ≤ Real.log l := Real.log_le_log hqlpos (by nlinarith)
    linarith
  have h214 : Real.log 2.14 ≤ 1.1 * Real.log 2 := by
    have := Real.log_le_log (show (0:ℝ) < 2.14 ^ 10 by positivity)
      (show (2.14:ℝ) ^ 10 ≤ 2 ^ 11 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hX1 : Real.log l - Real.log (q - l) ≤ 1.1 * Real.log 2 := by
    rw [← Real.log_div hlpos.ne' hqlpos.ne']
    have : (l:ℝ) / (q - l) ≤ 2.14 := by
      rw [div_le_iff₀ hqlpos]
      nlinarith
    linarith [Real.log_le_log (by positivity) this]
  have F4 : (l - q * ρ) * (Real.log l - Real.log (q - l)) ≤ 1.1 * Real.log 2 := by
    have : (l - q * ρ) * (Real.log l - Real.log (q - l)) ≤ Real.log l - Real.log (q - l) :=
      mul_le_of_le_one_left hX0 (by linarith)
    linarith
  linear_combination F1 + F2 + (q:ℝ) * F3 + F4

/-! ### Counting part of Lemma 2.5 (ii) -/

/-- Surjectivity of the Terras bijection (in the `pw` form). -/
theorem B_pw_surj (q : ℕ) (x : Fin q → Bool) : ∃ m < 2 ^ q, pw m q = x := by
  have hbij : Function.Bijective (fun m : Fin (2 ^ q) => pw (m : ℕ) q) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => Fin.ext (B_pw_inj a.isLt b.isLt h), ?_⟩
    simp
  obtain ⟨m, hm⟩ := hbij.2 x
  exact ⟨m, m.isLt, hm⟩

/-- Survival is monotone in the height. -/
theorem B_surv_mono {n : ℕ} (x : Fin n → Bool) {y y' : ℝ} (hyy : y ≤ y') (hs : SurvW y x) :
    SurvW y' x := by
  intro j h1 h2
  have := hs j h1 h2
  simp only [hw] at this ⊢
  linarith

/-- Counting part of Lemma 2.5 (ii): if the sum of a word with `l` ones is positive, then `C(q, l) ≤ q |E|`. -/
theorem B_choose_le_E (q l : ℕ) (hq : 0 < q) (y : ℝ) (hy : 0 ≤ y) (hl : (q:ℝ) < lam * l) :
    q.choose l ≤ q * (Eset q y).card := by
  classical
  set Dw := univ.filter (fun x : Fin q → Bool => ones x q = l) with hDw
  set Bw := univ.filter (fun x : Fin q → Bool => SurvW 0 x) with hBw
  have h1 : Dw.card ≤ Bw.card * q := by
    apply B_card_le_of_rot Dw Bw (fun b r => B_rot b (q - r))
    intro x hx
    rw [hDw, mem_filter] at hx
    obtain ⟨r, hr, hs⟩ := B_rot_surv hq x 0 le_rfl (by rw [hx.2]; linarith)
    exact ⟨r, hr, B_rot x r, by rw [hBw, mem_filter]; exact ⟨mem_univ _, hs⟩, B_rot_rot x r hr.le⟩
  have h2 : Bw ⊆ (Eset q y).image (fun z => pw z q) := by
    intro x hx
    rw [hBw, mem_filter] at hx
    obtain ⟨m, hm, rfl⟩ := B_pw_surj q x
    rw [mem_image]
    exact ⟨m, B_mem_Eset.mpr ⟨hm, B_surv_mono _ hy hx.2⟩, rfl⟩
  have h3 : Bw.card ≤ (Eset q y).card := le_trans (card_le_card h2) card_image_le
  calc q.choose l ≤ Dw.card := B_choose_le_words q l
    _ ≤ Bw.card * q := h1
    _ ≤ (Eset q y).card * q := Nat.mul_le_mul_right _ h3
    _ = q * (Eset q y).card := mul_comm _ _

/-! ## Lemma 2.3 (Chernoff) and Lemma 2.5 (ii)(iii) -/

/-- General form of Lemma 2.3: the number of `z ∈ E` (surviving from height `y ≥ 0`) such that `u_q(z)` begins with a word `w₁` of length `j` is
at most `2^{t*(y + a|w₁| − (j − |w₁|)) + (1−c)(q−j)}`. For `j = 0`, `|E| ≤ 2^{(1−c)q + t*y}`. -/
theorem chernoff (q : ℕ) (y : ℝ) (hy : 0 ≤ y) (j : ℕ) (hj : j ≤ q) (w₁ : Fin j → Bool) :
    (((Eset q y).filter (fun z => ∀ i : Fin j, pw z q ⟨i, by omega⟩ = w₁ i)).card : ℝ) ≤
      (2:ℝ) ^ (tstar * (y + aa * ones w₁ j - (j - ones w₁ j)) + (1 - cc) * (q - j)) := by
  set A : ℝ := (2:ℝ) ^ (tstar * aa) with hA
  set B : ℝ := (2:ℝ) ^ (-tstar) with hB
  set S := (Eset q y).filter (fun z => ∀ i : Fin j, pw z q ⟨i, by omega⟩ = w₁ i) with hS
  set F : (Fin q → Bool) → ℝ := fun x => (2:ℝ) ^ (tstar * y) * ∏ i, (if x i = true then A else B)
    with hF
  have hFnn : ∀ x, 0 ≤ F x := fun x => by
    simp only [hF]; apply mul_nonneg (by positivity)
    apply prod_nonneg; intro i _; split_ifs <;> positivity
  have hmemS : ∀ z ∈ S, z < 2 ^ q ∧ SurvW y (pw z q) ∧ ∀ i : Fin j, pw z q ⟨i, by omega⟩ = w₁ i := by
    intro z hz
    rw [hS, mem_filter, B_mem_Eset] at hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  have hinj : Set.InjOn (fun z => pw z q) (S : Set ℕ) := by
    intro z hz z' hz' h
    exact B_pw_inj (hmemS z hz).1 (hmemS z' hz').1 h
  have hsub : S.image (fun z => pw z q) ⊆ B_pre q j w₁ := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [B_mem_pre w₁ _ hj]
    exact (hmemS z hz).2.2
  have step1 : (S.card : ℝ) ≤ ∑ z ∈ S, F (pw z q) := by
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply sum_le_sum
    intro z hz
    exact B_weight_ge_one (pw z q) y hy (hmemS z hz).2.1
  have step2 : ∑ z ∈ S, F (pw z q) ≤ ∑ x ∈ B_pre q j w₁, F x := by
    rw [← sum_image hinj]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hFnn x)
  have step3 : ∑ x ∈ B_pre q j w₁, F x =
      (2:ℝ) ^ (tstar * y) * (A ^ (ones w₁ j) * B ^ (j - ones w₁ j)) * (A + B) ^ (q - j) := by
    simp only [hF]
    rw [← mul_sum, B_sum_pre q j hj w₁ A B, B_prod_ite]
    ring
  have hAB : A + B = (2:ℝ) ^ (1 - cc) := by
    have h17 := lemma17.1
    rw [← hA, ← hB] at h17
    have : A + B = 2 * ff := by linarith
    rw [this, ff, Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]
    field_simp
  have hle := B_ones_le w₁ j
  rw [step3, hAB] at step2
  refine le_trans step1 (le_trans step2 (le_of_eq ?_))
  rw [hA, hB, ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_mul_natCast (by norm_num),
    ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num), Nat.cast_sub hle, Nat.cast_sub hj]
  congr 1
  ring

/-- The case `j = 0` of Lemma 2.3: `|E| ≤ 2^{(1−c)q + t*y}`. -/
theorem E_upper (q : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    ((Eset q y).card : ℝ) ≤ (2:ℝ) ^ ((1 - cc) * q + tstar * y) := by
  have h := chernoff q y hy 0 (Nat.zero_le q) (fun i => i.elim0)
  have hf : (Eset q y).filter (fun z => ∀ i : Fin 0, pw z q ⟨i, by omega⟩ = (fun i => i.elim0) i) =
      Eset q y := by
    ext z; simp
  rw [hf, B_ones_zero] at h
  convert h using 2
  push_cast
  ring

/-- Lemma 2.5 (ii): if `q ≥ 20` and `y ≥ 0` then `|E| ≥ 2^{(1−c)q−1.1}/(q(q+1))`. -/
theorem E_lower (q : ℕ) (hq : 20 ≤ q) (y : ℝ) (hy : 0 ≤ y) :
    (2:ℝ) ^ ((1 - cc) * q - 1.1) / (q * (q + 1)) ≤ (Eset q y).card := by
  obtain ⟨hρ1, hρ2⟩ := rhoc_bounds
  have hlam := lam_bounds
  have hq' : (20:ℝ) ≤ q := by exact_mod_cast hq
  set l := ⌊(q:ℝ) * rhoc⌋₊ + 1 with hl
  have hlc : (l:ℝ) = ⌊(q:ℝ) * rhoc⌋₊ + 1 := by rw [hl]; push_cast; ring
  have hl1 : (q:ℝ) * rhoc < l := by rw [hlc]; exact Nat.lt_floor_add_one _
  have hl2 : (l:ℝ) ≤ q * rhoc + 1 := by
    rw [hlc]; linarith [Nat.floor_le (show (0:ℝ) ≤ q * rhoc by positivity)]
  have hlq : l < q := by
    have : (l:ℝ) < q := by nlinarith
    exact_mod_cast this
  -- Counting: `C(q, l) ≤ q |E|`
  have hsum : (q:ℝ) < lam * l := by
    have e : lam * rhoc = 1 := by
      rw [rhoc, mul_one_div, div_self (show (0:ℝ) < lam by linarith).ne']
    nlinarith
  have hc := B_choose_le_E q l (by omega) y hy hsum
  have hc' : (q.choose l : ℝ) ≤ q * (Eset q y).card := by exact_mod_cast hc
  -- Mode: `q^q ≤ (q+1) C(q,l) l^l (q−l)^{q−l}`
  have hm := B_mode q l hlq
  have hm' : (q:ℝ) ^ q ≤ (q + 1) * ((q.choose l : ℝ) * ((l:ℝ) ^ l * ((q - l : ℕ) : ℝ) ^ (q - l))) := by
    have : ((q ^ q : ℕ) : ℝ) ≤ (((q + 1) * B_U q l l : ℕ) : ℝ) := by exact_mod_cast hm
    simp only [B_U] at this
    push_cast at this
    linarith [this]
  have he := B_entropy q l hq hl1 hl2 hlq
  have hpos : (0:ℝ) < (l:ℝ) ^ l * ((q - l : ℕ) : ℝ) ^ (q - l) := by
    have : (0:ℝ) < ((q - l : ℕ) : ℝ) := by exact_mod_cast (show 0 < q - l by omega)
    have : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
    positivity
  -- `2^{(1−c)q−1.1} ≤ (q+1) C(q,l)`
  have hk : (2:ℝ) ^ ((1 - cc) * q - 1.1) ≤ (q + 1) * (q.choose l : ℝ) := by
    have h1 := le_trans he hm'
    have h2 : (2:ℝ) ^ ((1 - cc) * q - 1.1) * ((l:ℝ) ^ l * ((q - l : ℕ) : ℝ) ^ (q - l)) ≤
        ((q + 1) * (q.choose l : ℝ)) * ((l:ℝ) ^ l * ((q - l : ℕ) : ℝ) ^ (q - l)) := by
      linarith [h1]
    exact le_of_mul_le_mul_right h2 hpos
  have hqq : (0:ℝ) < q * (q + 1) := by positivity
  rw [div_le_iff₀ hqq]
  calc (2:ℝ) ^ ((1 - cc) * q - 1.1) ≤ (q + 1) * (q.choose l : ℝ) := hk
    _ ≤ (q + 1) * (q * (Eset q y).card) := by gcongr
    _ = (Eset q y).card * (q * (q + 1)) := by ring

/-- `ρ̄ = (L' − 1)/(t − 1)` (§6). -/
noncomputable def rhoBar (q s L P : ℕ) : ℝ := ((L - Lp q - 1 : ℕ) : ℝ) / ((s - P - 1 : ℕ) : ℝ)

/-- Lemma 2.5 (iii): if `t ≥ 2`, `h_L ≥ 0`, and `𝒯 ≠ ∅`, then `|𝒯| ≥ C(t−1, L'−1)/(t−1)`. -/
theorem T_lower (q s L P : ℕ) (ht : 2 ≤ s - P) (hL0 : 0 ≤ hL s L) (hne : (Tset q s L P).Nonempty) :
    (Nat.choose (s - P - 1) (L - Lp q - 1) : ℝ) / (s - P - 1 : ℕ) ≤ (Tset q s L P).card := by
  obtain ⟨τ₀, hτ₀⟩ := hne
  rw [B_mem_Tset] at hτ₀
  obtain ⟨h0, hones, hsurv⟩ := hτ₀
  have hpos : 0 < s - P := by omega
  -- The first letter is 1, so `L − L_p ≥ 1`, and the height at time 1 gives `h_p + a ≥ 0`
  have hone1 : ones τ₀ 1 = 1 := by
    unfold ones
    rw [card_eq_one]
    refine ⟨⟨0, hpos⟩, ?_⟩
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨h1, _⟩; exact Fin.ext (by dsimp only; omega)
    · rintro rfl; exact ⟨by simp, h0 hpos⟩
  have hLL : 1 ≤ L - Lp q := by
    rw [← hones]
    calc 1 = ones τ₀ 1 := hone1.symm
      _ ≤ ones τ₀ (s - P) := by
        unfold ones
        apply card_le_card
        intro i
        simp only [mem_filter, mem_univ, true_and]
        rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  have hy : 0 ≤ hp q P + aa := by
    have := hsurv 1 le_rfl (by omega)
    simp only [hw, hone1, aa] at this ⊢
    push_cast at this
    linarith
  apply B_T_aux (s - P) (s - P - 1) (L - Lp q - 1) (by omega) (by omega) (hp q P) hy
  · have e1 : ((L - Lp q - 1 : ℕ) : ℝ) = L - Lp q - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have e2 : ((s - P - 1 : ℕ) : ℝ) = s - P - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [e1, e2]
    simp only [hp, aa, hL] at hL0 ⊢
    linarith
  · intro τ h1 h2 h3
    rw [B_mem_Tset]
    exact ⟨h1, by rw [h2]; omega, h3⟩

end Collatz.M1
