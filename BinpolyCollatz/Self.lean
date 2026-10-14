import BinpolyCollatz.Tri

namespace BinpolyCollatz
open Polynomial

/-- If `F_j = (x+1)^v Q` with `Q(1) = 1` and `j ≥ 1`, then `T(x^{j+3}+x+1) = Q` and `Q` is odd. -/
lemma T_tri_of {j v : ℕ} {Q : P} (hj : 1 ≤ j) (hQ1 : Q.eval 1 = 1) (hF : F j = (X + 1) ^ v * Q) :
    T (tri (j + 3)) = Q ∧ IsOdd Q := by
  have hQ0 : Q.eval 0 = 1 := by
    have := eval_zero_F hj
    rw [hF, eval_mul, eval_pow, eval_add, eval_X, eval_one, zero_add, one_pow, one_mul] at this
    exact this
  have hQ : IsOdd Q := ⟨hQ0, hQ1⟩
  refine ⟨?_, hQ⟩
  rw [tri, lem_Tri (by omega), Nat.add_sub_cancel, hF]
  have := op_of_eq (a := 0) (b := v) hQ
  rwa [pow_zero, one_mul, X_sub_C_one] at this

/-- If `(x+1)^v (1 + M Q) = x^c F_h²` then `T(Q) = op(F_h)²`. -/
lemma T_Q_of {v c h : ℕ} {Q : P} (hid : (X + 1) ^ v * (1 + M * Q) = X ^ c * F h ^ 2) :
    T Q = op (F h) ^ 2 := by
  rw [T, ← op_X1_pow_mul (b := v) (one_add_M_mul_ne_zero Q), hid,
    op_X_pow_mul (pow_ne_zero _ (F_ne_zero h)), op_pow (F_ne_zero h)]

/-- The index `m(n)` of Proposition `prop:self`. -/
def mSelf (n : ℕ) : ℕ :=
  if n % 2 = 1 then (n + 1) / 2 else if n % 4 = 2 then (n + 2) / 2 else n / 2

/-- **Proposition `prop:self`.** For `n ≥ 5`, `3 ≤ m(n) < n` and
`T²(x^n+x+1) = T(x^{m(n)}+x+1)²`. -/
theorem prop_self {n : ℕ} (hn : 5 ≤ n) :
    3 ≤ mSelf n ∧ mSelf n < n ∧ T (T (X ^ n + X + 1)) = T (X ^ mSelf n + X + 1) ^ 2 := by
  refine ⟨by unfold mSelf; split_ifs <;> omega, by unfold mSelf; split_ifs <;> omega, ?_⟩
  change T (T (tri n)) = T (tri (mSelf n)) ^ 2
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' k
    · -- n ≡ 0 (mod 4): n = 4i'+8, j = 4(i'+1)+1, h = 2i'+1, c = 3
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
      have hm : mSelf n = 2 * i' + 1 + 3 := by unfold mSelf; split_ifs <;> omega
      obtain ⟨Q, hQ1, hF⟩ := decomp_one (i' + 1)
      have hn' : n = (4 * (i' + 1) + 1) + 3 := by omega
      obtain ⟨hT, -⟩ := T_tri_of (by omega) hQ1 hF
      rw [hm, hn', hT, tri, lem_Tri (by omega), Nat.add_sub_cancel]
      apply T_Q_of (v := 3) (c := 3)
      rw [F] at hF ⊢; rw [M] at *
      linear_combination (norm := ring2) (X ^ 2 + X + 1) * hF
    · -- n ≡ 2 (mod 4): n = 4i+6, j = 4i+3, h = 2i+1, c = 1
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hm : mSelf n = 2 * i' + 1 + 3 := by unfold mSelf; split_ifs <;> omega
      obtain ⟨Q, hQ1, hF⟩ := decomp_three i'
      have hn' : n = (4 * i' + 3) + 3 := by omega
      obtain ⟨hT, -⟩ := T_tri_of (by omega) hQ1 hF
      rw [hm, hn', hT, tri, lem_Tri (by omega), Nat.add_sub_cancel]
      apply T_Q_of (v := 2) (c := 1)
      rw [F] at hF ⊢; rw [M] at *
      linear_combination (norm := ring2) (X ^ 2 + X + 1) * hF
  · -- n odd: n = 2h+5, j = 2(h+1), c = 2
    obtain ⟨h, rfl⟩ : ∃ h, k = h + 2 := ⟨k - 2, by omega⟩
    have hm : mSelf n = h + 3 := by unfold mSelf; split_ifs <;> omega
    obtain ⟨Q, hQ1, hF⟩ := decomp_even (h + 1)
    have hn' : n = 2 * (h + 1) + 3 := by omega
    obtain ⟨hT, -⟩ := T_tri_of (j := 2 * (h + 1)) (by omega) hQ1 (v := 1)
      (by rw [pow_one]; exact hF)
    rw [hm, hn', hT, tri, lem_Tri (by omega), Nat.add_sub_cancel]
    apply T_Q_of (v := 1) (c := 2)
    rw [F] at hF ⊢; rw [M] at *
    linear_combination (norm := ring2) (X ^ 2 + X + 1) * hF

/-- Uniform description of `O₁(n) = T(x^n+x+1)` for `n ≥ 4`: `F_{n-3} = (x+1)^v O₁(n)` with
`v = v_{x+1}(F_{n-3}) ∈ {1,2,3}` and `O₁(n)` odd. -/
lemma T_tri_decomp {n : ℕ} (hn : 4 ≤ n) :
    ∃ v, 1 ≤ v ∧ v ≤ 3 ∧ F (n - 3) = (X + 1) ^ v * T (tri n) ∧ IsOdd (T (tri n)) ∧
      (v = if (n - 3) % 2 = 0 then 1 else if (n - 3) % 4 = 3 then 2 else 3) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' j
  · subst hk
    obtain ⟨Q, hQ1, hF⟩ := decomp_even k
    obtain ⟨hT, hQ⟩ := T_tri_of (j := 2 * k) (by omega) hQ1 (v := 1) (by rw [pow_one]; exact hF)
    refine ⟨1, le_rfl, by norm_num, ?_, ?_, ?_⟩
    · rw [hT, pow_one, hF]
    · rw [hT]; exact hQ
    · split_ifs <;> omega
  · obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' k
    · have hj : j = 4 * i + 1 := by omega
      subst hj
      obtain ⟨Q, hQ1, hF⟩ := decomp_one i
      obtain ⟨hT, hQ⟩ := T_tri_of (by omega) hQ1 hF
      refine ⟨3, by norm_num, le_rfl, ?_, ?_, ?_⟩
      · rw [hT, hF]
      · rw [hT]; exact hQ
      · split_ifs <;> omega
    · have hj : j = 4 * i + 3 := by omega
      subst hj
      obtain ⟨Q, hQ1, hF⟩ := decomp_three i
      obtain ⟨hT, hQ⟩ := T_tri_of (by omega) hQ1 hF
      refine ⟨2, by norm_num, by norm_num, ?_, ?_, ?_⟩
      · rw [hT, hF]
      · rw [hT]; exact hQ
      · split_ifs <;> omega

/-- `e_n = deg O₁(n) = n - 1 - v`. -/
lemma natDegree_T_tri {n : ℕ} (hn : 4 ≤ n) :
    ∃ v, 1 ≤ v ∧ v ≤ 3 ∧ (T (tri n)).natDegree + v + 1 = n ∧
      (v = if (n - 3) % 2 = 0 then 1 else if (n - 3) % 4 = 3 then 2 else 3) := by
  obtain ⟨v, hv1, hv3, hF, hO, hv⟩ := T_tri_decomp hn
  refine ⟨v, hv1, hv3, ?_, hv⟩
  have := congrArg natDegree hF
  have hX1 : (X + 1 : P) ≠ 0 := by rw [← X_sub_C_one]; exact X_sub_C_ne_zero _
  rw [natDegree_F, natDegree_mul (pow_ne_zero _ hX1) hO.ne_zero, natDegree_pow,
    show (X + 1 : P).natDegree = 1 by compute_degree!] at this
  omega

lemma T_tri_ne_one {n : ℕ} (hn : 5 ≤ n) : T (tri n) ≠ 1 := by
  obtain ⟨v, -, hv3, hd, -⟩ := natDegree_T_tri (n := n) (by omega)
  intro h; rw [h, natDegree_one] at hd; omega

lemma T_tri_three : T (tri 3) = 1 := by
  rw [tri, lem_Tri le_rfl, Nat.sub_self, F_zero, show y = y * 1 by ring, op_y_mul one_ne_zero, op_one]

lemma T_tri_four : T (tri 4) = 1 := by
  rw [tri, lem_Tri (by norm_num), show 4 - 3 = 1 by rfl,
    show F 1 = (X + 1) ^ 3 * 1 by rw [F, M]; ring2, op_X1_pow_mul one_ne_zero, op_one]

lemma sigma_tri_small {n : ℕ} (hn : n = 3 ∨ n = 4) : sigma (tri n) = 1 := by
  rw [sigma_succ (isOdd_tri (by omega)) (tri_ne_one (by omega))]
  rcases hn with rfl | rfl
  · rw [T_tri_three, sigma_one]
  · rw [T_tri_four, sigma_one]

lemma sigma_tri_rec {n : ℕ} (hn : 5 ≤ n) : sigma (tri n) = 2 * sigma (tri (mSelf n)) := by
  obtain ⟨hm3, -, hself⟩ := prop_self hn
  change T (T (tri n)) = T (tri (mSelf n)) ^ 2 at hself
  have hO1 : IsOdd (T (tri n)) := isOdd_T _
  rw [sigma_succ (isOdd_tri (by omega)) (tri_ne_one (by omega)),
    sigma_succ hO1 (T_tri_ne_one hn), hself, (lem_square (isOdd_T (tri (mSelf n)))).2.2.1,
    sigma_succ (isOdd_tri (by omega)) (tri_ne_one (by omega))]
  ring

lemma clog_mSelf {n : ℕ} (hn : 5 ≤ n) :
    3 ≤ Nat.clog 2 n ∧ Nat.clog 2 (mSelf n) = Nat.clog 2 n - 1 := by
  have hk3 : 3 ≤ Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by norm_num; omega)
  obtain ⟨k', hk'⟩ : ∃ k', Nat.clog 2 n = k' + 3 := ⟨Nat.clog 2 n - 3, by omega⟩
  have hup : n ≤ 2 ^ (k' + 3) := hk' ▸ Nat.le_pow_clog (by norm_num) n
  have hlow : 2 ^ (k' + 2) < n := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by omega)
    rwa [hk'] at this
  refine ⟨hk3, ?_⟩
  rw [hk', show k' + 3 - 1 = k' + 2 by omega]
  have e1 : 2 ^ (k' + 3) = 8 * 2 ^ k' := by ring
  have e2 : 2 ^ (k' + 2) = 4 * 2 ^ k' := by ring
  have e3 : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
  rw [e1] at hup; rw [e2] at hlow
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num), e2]
    unfold mSelf; split_ifs <;> omega
  · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num), e3]
    unfold mSelf; split_ifs <;> omega

lemma sigma_tri {n : ℕ} (hn : 3 ≤ n) : sigma (tri n) = 2 ^ (Nat.clog 2 n - 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h5 : n ≤ 4
    · rw [sigma_tri_small (by omega)]
      have : Nat.clog 2 n = 2 := by
        apply le_antisymm
        · rw [Nat.clog_le_iff_le_pow (by norm_num)]; norm_num; omega
        · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]; norm_num; omega
      rw [this]; rfl
    · have hn5 : 5 ≤ n := by omega
      obtain ⟨hm3, hmn, -⟩ := prop_self hn5
      obtain ⟨hk3, hk⟩ := clog_mSelf hn5
      rw [sigma_tri_rec hn5, ih _ hmn hm3, hk, ← pow_succ']
      congr 1; omega

/-- **Theorem `thm:tri`** (Theorem A, length). For `n ≥ 3`, the odd sequence of `x^n + x + 1`
has length `2^(⌈log₂ n⌉ - 2) + 1`. -/
theorem thm_tri {n : ℕ} (hn : 3 ≤ n) :
    oddLength (X ^ n + X + 1) = 2 ^ (Nat.clog 2 n - 2) + 1 := by
  change sigma (op (tri n)) + 1 = _
  rw [op_eq_self (isOdd_tri (by omega)), sigma_tri hn]

end BinpolyCollatz
