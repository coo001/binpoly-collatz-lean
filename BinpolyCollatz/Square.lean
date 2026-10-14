import BinpolyCollatz.Bound

namespace BinpolyCollatz
open Polynomial

/-- Normalise a commutative-ring identity and reduce numerals modulo 2. -/
macro "ring2" : tactic => `(tactic| (ring_nf <;> (try reduce_mod_char) <;> (try ring_nf)))

lemma sq_add (a b : P) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by ring2

lemma eq_one_of_sq_eq_one {W : P} (h : W ^ 2 = 1) : W = 1 := by
  have : (W + 1) ^ 2 = 0 := by rw [sq_add, h]; ring2
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linear_combination this - two_eq_zero_P

lemma sigma_succ {O : P} (hO : IsOdd O) (h1 : O ≠ 1) : sigma O = sigma (T O) + 1 := by
  rw [sigma_eq_iff hO]
  obtain ⟨hs1, hs2⟩ := sigma_spec (isOdd_T O)
  refine ⟨by rw [Function.iterate_succ_apply]; exact hs1, fun m hm => ?_⟩
  rcases m with _ | m
  · simpa using h1
  · rw [Function.iterate_succ_apply]; exact hs2 m (by omega)

lemma sigma_one : sigma 1 = 0 := (sigma_eq_iff isOdd_one).2 ⟨rfl, fun _ h => absurd h (by omega)⟩

lemma T_one : T 1 = 1 := by
  rw [T, mul_one, one_add_M, show y = y * 1 by ring, op_y_mul one_ne_zero, op_one]

lemma square_step {U : P} (hU : IsOdd U) :
    U + 1 = y * ((U + 1) /ₘ y) ∧
    T (U ^ 2) = 1 + y * M * ((U + 1) /ₘ y) ^ 2 ∧ T (T (U ^ 2)) = T U ^ 2 := by
  obtain ⟨K, hK⟩ := y_dvd_of_isOdd hU
  have hKK : (U + 1) /ₘ y = K := by rw [hK, mul_divByMonic_cancel_left _ monic_y]
  rw [hKK]
  have hV : T (U ^ 2) = 1 + y * M * K ^ 2 := by
    rw [T_eq_of (K := y * K ^ 2) (by rw [show U ^ 2 + 1 = (U + 1) ^ 2 by rw [sq_add, one_pow], hK]; ring)]
    rw [show 1 + M * (y * K ^ 2) = 1 + y * M * K ^ 2 by ring]
    apply op_eq_self; simp [IsOdd]
  refine ⟨hK, hV, ?_⟩
  rw [hV, T_eq_of (K := M * K ^ 2) (by ring2), T_eq_of hK,
    show 1 + M * (M * K ^ 2) = (1 + M * K) ^ 2 by rw [sq_add]; ring,
    op_pow (one_add_M_mul_ne_zero K)]

lemma iterate_sq {U : P} (hU : IsOdd U) (k : ℕ) : T^[2 * k] (U ^ 2) = (T^[k] U) ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, (square_step (isOdd_iterate_T hU k)).2.2,
      Function.iterate_succ_apply']

lemma natDegree_T_sq {W : P} (hW : IsOdd W) : (T (W ^ 2)).natDegree = 2 * W.natDegree := by
  obtain ⟨hK, hV, -⟩ := square_step hW
  set K := (W + 1) /ₘ y
  by_cases hK0 : K = 0
  · have : W = 1 := by rw [hK0, mul_zero] at hK; linear_combination hK - two_eq_zero_P
    subst this; simp [T_one]
  · have hW' : W = 1 + y * K := by linear_combination hK - two_eq_zero_P
    rw [hV, natDegree_one_add, hW', natDegree_one_add]
    all_goals
      first
      | rw [natDegree_mul (mul_ne_zero y_ne_zero M_ne_zero) (pow_ne_zero _ hK0),
          natDegree_mul y_ne_zero M_ne_zero, natDegree_pow, natDegree_mul y_ne_zero hK0,
          natDegree_y, natDegree_M]; omega
      | rw [natDegree_mul y_ne_zero hK0, natDegree_y]; omega
      | rw [natDegree_mul (mul_ne_zero y_ne_zero M_ne_zero) (pow_ne_zero _ hK0),
          natDegree_mul y_ne_zero M_ne_zero, natDegree_pow, natDegree_y, natDegree_M]; omega

lemma T_sq_ne_one {W : P} (hW : IsOdd W) (h1 : W ≠ 1) : T (W ^ 2) ≠ 1 := by
  intro h
  have := natDegree_T_sq hW
  rw [h, natDegree_one] at this
  exact h1 (eq_one_of_isOdd_natDegree_le_one hW (by omega))

/-- **Lemma `lem:square`.** Let `U` be odd and `K = (U+1)/y`. Then `T(U²) = 1 + y M K²`,
`T²(U²) = T(U)²`, `σ(U²) = 2σ(U)`, and the degree sequence of `U²` is that of `U` with every
entry doubled and each non-final entry repeated twice. -/
theorem lem_square {U : P} (hU : IsOdd U) :
    let K := (U + 1) /ₘ y
    T (U ^ 2) = 1 + y * M * K ^ 2 ∧ T (T (U ^ 2)) = T U ^ 2 ∧
    sigma (U ^ 2) = 2 * sigma U ∧
    (∀ k, (T^[2 * k] (U ^ 2)).natDegree = 2 * (T^[k] U).natDegree) ∧
    (∀ k, (T^[2 * k + 1] (U ^ 2)).natDegree = 2 * (T^[k] U).natDegree) := by
  intro K
  obtain ⟨-, h1, h2⟩ := square_step hU
  refine ⟨h1, h2, ?_, fun k => ?_, fun k => ?_⟩
  · rw [sigma_eq_iff (hU.pow 2)]
    obtain ⟨hs1, hs2⟩ := sigma_spec hU
    refine ⟨by rw [iterate_sq hU, hs1, one_pow], fun m hm => ?_⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [iterate_sq hU]; intro h; exact hs2 k (by omega) (eq_one_of_sq_eq_one h)
    · rw [Function.iterate_succ_apply', iterate_sq hU]
      exact T_sq_ne_one (isOdd_iterate_T hU k) (hs2 k (by omega))
  · rw [iterate_sq hU, natDegree_pow]
  · rw [Function.iterate_succ_apply', iterate_sq hU, natDegree_T_sq (isOdd_iterate_T hU k)]

end BinpolyCollatz
