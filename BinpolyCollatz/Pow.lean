import BinpolyCollatz.Square

namespace BinpolyCollatz
open Polynomial

lemma M_pow_add_one_ne_zero {n : ℕ} (hn : 1 ≤ n) : M ^ n + 1 ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_zero, add_comm, natDegree_one_add] at this <;>
    rw [natDegree_pow, natDegree_M] at * <;> omega

/-- `S_n = ∑_{i<n} M^i`, with `y S_n = M^n + 1`. -/
noncomputable def S (n : ℕ) : P := ∑ i ∈ Finset.range n, M ^ i

lemma y_mul_S (n : ℕ) : y * S n = M ^ n + 1 := by
  have := geom_sum_mul M n
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, M_add_one] at this
  rw [mul_comm]; exact this

lemma isOdd_S {k : ℕ} : IsOdd (S (2 * k + 1)) := by
  have h : ∀ a : ZMod 2, a = 1 → (S (2 * k + 1)).eval a = 1 := by
    rintro a rfl
    simp only [S, eval_finset_sum, eval_pow, eval_one_M, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast; rw [show (2 : ZMod 2) = 0 by decide]; simp
  refine ⟨?_, h 1 rfl⟩
  simp only [S, eval_finset_sum, eval_pow, eval_zero_M, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast; rw [show (2 : ZMod 2) = 0 by decide]; simp

/-- `D(n) = σ(op(M^n + 1))`. -/
noncomputable def D (n : ℕ) : ℕ := sigma (op (M ^ n + 1))

lemma D_one : D 1 = 0 := by
  rw [D, pow_one, M_add_one, show y = y * 1 by ring, op_y_mul one_ne_zero, op_one, sigma_one]

lemma D_double {n : ℕ} (hn : 1 ≤ n) : D (2 * n) = 2 * D n := by
  have h0 := M_pow_add_one_ne_zero hn
  rw [D, D, show M ^ (2 * n) + 1 = (M ^ n + 1) ^ 2 by rw [sq_add, ← pow_mul, mul_comm]; ring,
    op_pow h0, (lem_square (op_isOdd h0)).2.2.1]

lemma D_odd {k : ℕ} (hk : 1 ≤ k) : D (2 * k + 1) = 1 + D (2 * k + 2) := by
  have hS := isOdd_S (k := k)
  have hP : op (M ^ (2 * k + 1) + 1) = S (2 * k + 1) := by
    rw [← y_mul_S, op_y_mul hS.ne_zero, op_eq_self hS]
  have hT : T (S (2 * k + 1)) = op (M ^ (2 * k + 2) + 1) := by
    rw [T, ← op_y_mul (one_add_M_mul_ne_zero _)]
    congr 1
    have := y_mul_S (2 * k + 1)
    rw [← M_add_one] at this ⊢
    linear_combination (norm := ring2) M * this
  have hS1 : S (2 * k + 1) ≠ 1 := by
    intro h
    have := y_mul_S (2 * k + 1)
    rw [h, mul_one] at this
    have := congrArg natDegree this
    rw [natDegree_y, add_comm, natDegree_one_add, natDegree_pow, natDegree_M] at this <;>
      [omega; (rw [natDegree_pow, natDegree_M]; omega)]
  rw [D, D, hP, sigma_succ hS hS1, hT, add_comm]

lemma clog_two_mul {k : ℕ} (hk : 1 ≤ k) : Nat.clog 2 (2 * k) = Nat.clog 2 k + 1 := by
  have h1 : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by norm_num) k
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ]; omega
  · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]
    rcases Nat.eq_zero_or_pos (Nat.clog 2 k) with h0 | h0
    · rw [h0]; omega
    · have hk2 : 1 < k := by
        by_contra h
        have : k = 1 := by omega
        subst this; simp at h0
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hk2
      have e : 2 ^ Nat.clog 2 k = 2 * 2 ^ (Nat.clog 2 k).pred := by
        rw [← pow_succ']; congr 1; rw [Nat.pred_eq_sub_one]; omega
      omega

lemma D_eq {n : ℕ} (hn : 1 ≤ n) : D n = 2 ^ Nat.clog 2 n - n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst hk
    have hk1 : 1 ≤ k := by omega
    rw [D_double hk1, ih k (by omega) hk1, clog_two_mul hk1, pow_succ]
    have := Nat.le_pow_clog (b := 2) (by norm_num) k
    omega
  · subst hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [D_one]; simp
    · rw [D_odd h0, show 2 * k + 2 = 2 * (k + 1) by ring, D_double (by omega),
        ih (k + 1) (by omega) (by omega)]
      have hc : Nat.clog 2 (2 * k + 1) = Nat.clog 2 (k + 1) + 1 := by
        have h1 : k + 1 ≤ 2 ^ Nat.clog 2 (k + 1) := Nat.le_pow_clog (by norm_num) _
        have h2 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := k + 1) (by omega)
        have hpos : 0 < Nat.clog 2 (k + 1) := Nat.clog_pos (by norm_num) (by omega)
        have e : 2 ^ Nat.clog 2 (k + 1) = 2 * 2 ^ (Nat.clog 2 (k + 1)).pred := by
          rw [← pow_succ']; congr 1; rw [Nat.pred_eq_sub_one]; omega
        apply le_antisymm
        · rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ]; omega
        · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]; omega
      rw [hc, pow_succ]
      have := Nat.le_pow_clog (b := 2) (by norm_num) (k + 1)
      omega

/-- **Theorem `thm:pow`** (Theorem B). For every `n ≥ 1` the odd sequence of `M^n + 1` has length
`2^⌈log₂ n⌉ - n + 1`. -/
theorem thm_pow {n : ℕ} (hn : 1 ≤ n) : oddLength (M ^ n + 1) = 2 ^ Nat.clog 2 n - n + 1 := by
  rw [oddLength, ← D, D_eq hn]

end BinpolyCollatz
