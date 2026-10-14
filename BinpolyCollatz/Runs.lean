import BinpolyCollatz.Basic

namespace BinpolyCollatz
open Polynomial

lemma add_one_add_one (p : P) : p + 1 + 1 = p := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

lemma one_add_M_mul_ne_zero (K : P) : 1 + M * K ≠ 0 := by
  intro h
  have h' : M * K = 1 := by linear_combination h - two_eq_zero_P
  have hK : K ≠ 0 := by rintro rfl; simp at h'
  have := congrArg natDegree h'
  rw [natDegree_mul M_ne_zero hK, natDegree_M] at this; simp at this

/-- `T` always produces an odd polynomial. -/
lemma isOdd_T (O : P) : IsOdd (T O) := by
  rw [T]; apply op_isOdd
  exact one_add_M_mul_ne_zero O

lemma isOdd_iterate_T {O : P} (hO : IsOdd O) (k : ℕ) : IsOdd (T^[k] O) := by
  cases k with
  | zero => exact hO
  | succ k => rw [Function.iterate_succ_apply']; exact isOdd_T _

/-- Core of Lemma `lem:T`: if `O + 1 = y K` then `T(O) = op(1 + M K)`. -/
lemma T_eq_of {O K : P} (hK : O + 1 = y * K) : T O = op (1 + M * K) := by
  have e : 1 + M * O = y * (1 + M * K) := by
    linear_combination M * hK + one_add_M - M * two_eq_zero_P
  rw [T, e, op_y_mul (one_add_M_mul_ne_zero K)]

lemma y_dvd_of_isOdd {O : P} (hO : IsOdd O) : y ∣ O + 1 := by
  have h0 : (X - C 0 : P) ∣ O + 1 := by
    rw [dvd_iff_isRoot]; simp [IsRoot, hO.1]; decide
  have h1 : (X - C 1 : P) ∣ O + 1 := by
    rw [dvd_iff_isRoot]; simp [IsRoot, hO.2]; decide
  have := isCoprime_X_X1.mul_dvd h0 h1
  rwa [X_sub_C_zero, X_sub_C_one] at this

/-- **Lemma `lem:T`.** For odd `O`, `y ∣ O + 1` and `T(O) = op(1 + M (O+1)/y)`. -/
theorem lem_T {O : P} (hO : IsOdd O) :
    y ∣ O + 1 ∧ T O = op (1 + M * ((O + 1) /ₘ y)) := by
  refine ⟨y_dvd_of_isOdd hO, T_eq_of ?_⟩
  obtain ⟨K, hK⟩ := y_dvd_of_isOdd hO
  rw [hK, mul_divByMonic_cancel_left _ monic_y]

lemma natDegree_one_add {p : P} (h : 1 ≤ p.natDegree) : (1 + p).natDegree = p.natDegree := by
  apply natDegree_add_eq_right_of_natDegree_lt; simp; omega

lemma natDegree_MyK (i j : ℕ) {K : P} (hK : K ≠ 0) :
    (M ^ i * y ^ j * K).natDegree = 2 * i + 2 * j + K.natDegree := by
  rw [natDegree_mul (mul_ne_zero (pow_ne_zero _ M_ne_zero) (pow_ne_zero _ y_ne_zero)) hK,
    natDegree_mul (pow_ne_zero _ M_ne_zero) (pow_ne_zero _ y_ne_zero), natDegree_pow, natDegree_pow,
    natDegree_M, natDegree_y]
  ring

/-- Core run computation: if `O + 1 = y^L K` with `L ≥ 1`, `K ≠ 0` and `K` not divisible by
both `x` and `x+1`, then `T^i O = 1 + M^i y^(L-i) K` has degree `deg O` for `i < L`
and `deg T^L O < deg O`. -/
lemma runs_core {O K : P} {L : ℕ} (hL : 1 ≤ L) (hK0 : K ≠ 0) (hOK : O + 1 = y ^ L * K)
    (hKr : K.eval 0 ≠ 0 ∨ K.eval 1 ≠ 0) :
    O.natDegree = 2 * L + K.natDegree ∧
    (∀ i < L, T^[i] O = 1 + M ^ i * y ^ (L - i) * K ∧ (T^[i] O).natDegree = O.natDegree) ∧
    (T^[L] O).natDegree < O.natDegree := by
  have hO : O = 1 + M ^ 0 * y ^ L * K := by
    linear_combination hOK - two_eq_zero_P
  have hdeg : O.natDegree = 2 * L + K.natDegree := by
    rw [hO, natDegree_one_add] <;> rw [natDegree_MyK _ _ hK0] <;> omega
  -- the step
  have step : ∀ i, i < L → T^[i] O = 1 + M ^ i * y ^ (L - i) * K →
      T^[i + 1] O = op (1 + M ^ (i + 1) * y ^ (L - (i + 1)) * K) := by
    intro i hi h
    rw [Function.iterate_succ_apply', h]
    apply Eq.trans (T_eq_of (K := M ^ i * y ^ (L - (i + 1)) * K) _)
    · congr 1; ring
    · have : L - i = (L - (i + 1)) + 1 := by omega
      rw [this]; linear_combination two_eq_zero_P
  have form : ∀ i, i < L → T^[i] O = 1 + M ^ i * y ^ (L - i) * K := by
    intro i
    induction i with
    | zero => intro _; simpa using hO
    | succ i ih =>
      intro hi
      rw [step i (by omega) (ih (by omega))]
      apply op_eq_self
      have hpos : L - (i + 1) ≠ 0 := by omega
      simp [IsOdd, eval_pow, hpos]
  refine ⟨hdeg, fun i hi => ⟨form i hi, ?_⟩, ?_⟩
  · rw [form i hi, natDegree_one_add] <;> rw [natDegree_MyK _ _ hK0] <;> omega
  · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [step L' (by omega) (form L' (by omega)), Nat.sub_self, pow_zero, mul_one]
    have hQdeg : (1 + M ^ (L' + 1) * K).natDegree = O.natDegree := by
      rw [hdeg, natDegree_one_add] <;>
        rw [natDegree_mul (pow_ne_zero _ M_ne_zero) hK0, natDegree_pow, natDegree_M] <;> omega
    rw [← hQdeg]
    apply natDegree_op_lt
    · intro h; rw [h] at hQdeg; simp at hQdeg; omega
    · rintro ⟨h0, h1⟩
      simp only [eval_add, eval_one, eval_mul, eval_pow, eval_zero_M, eval_one_M, one_pow,
        one_mul] at h0 h1
      rcases hKr with h | h
      · exact h (by have := zmod2_eq_one h; rw [this] at h0; exact absurd h0 (by decide))
      · exact h (by have := zmod2_eq_one h; rw [this] at h1; exact absurd h1 (by decide))

/-- **Lemma `lem:runs`.** Let `O` be odd of degree `d ≥ 2`,
`L = min(v_x(O+1), v_{x+1}(O+1))`, `K = (O+1)/y^L`. Then `1 ≤ L ≤ ⌊d/2⌋`;
for `0 ≤ i < L`, `T^i(O) = 1 + M^i y^(L-i) K` has degree `d`; and `deg T^L(O) < d`. -/
theorem lem_runs {O : P} (hO : IsOdd O) (hd : 2 ≤ O.natDegree) :
    let L := min ((O + 1).rootMultiplicity 0) ((O + 1).rootMultiplicity 1)
    let K := (O + 1) /ₘ y ^ L
    1 ≤ L ∧ L ≤ O.natDegree / 2 ∧
    (∀ i < L, T^[i] O = 1 + M ^ i * y ^ (L - i) * K ∧ (T^[i] O).natDegree = O.natDegree) ∧
    (T^[L] O).natDegree < O.natDegree := by
  intro L K
  have hne : O + 1 ≠ 0 := by
    intro h
    have : O = 1 := by linear_combination h - two_eq_zero_P
    rw [this] at hd; simp at hd
  have hspec := op_spec hne
  set a := (O + 1).rootMultiplicity 0
  set b := (O + 1).rootMultiplicity 1
  have ha : 1 ≤ a := (rootMultiplicity_pos hne).2 (by simp [IsRoot, hO.1]; decide)
  have hb : 1 ≤ b := (rootMultiplicity_pos hne).2 (by simp [IsRoot, hO.2]; decide)
  set R := op (O + 1)
  have hR : IsOdd R := op_isOdd hne
  set K' : P := (X - C 0) ^ (a - L) * (X - C 1) ^ (b - L) * R
  have hK'0 : K' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _)))
      hR.ne_zero
  have hOK : O + 1 = y ^ L * K' := by
    have ea : a = L + (a - L) := by omega
    have eb : b = L + (b - L) := by omega
    conv_lhs => rw [hspec, ea, eb]
    simp only [K', y, X_sub_C_zero, X_sub_C_one, mul_pow]; ring
  have hKK : K = K' := by
    simp only [K]; rw [hOK, mul_divByMonic_cancel_left _ (monic_y.pow L)]
  have hKr : K'.eval 0 ≠ 0 ∨ K'.eval 1 ≠ 0 := by
    rcases min_choice a b with h | h
    · left; have : a - L = 0 := by simp only [L]; omega
      simp [K', this, hR.1]
    · right; have : b - L = 0 := by simp only [L]; omega
      simp [K', this, hR.2]
  have hL : 1 ≤ L := le_min ha hb
  obtain ⟨hdeg, hiter, hlast⟩ := runs_core hL hK'0 hOK hKr
  rw [hKK]
  exact ⟨hL, by omega, hiter, hlast⟩

/-- Run bound: a run of consecutive terms `T^i O`, `0 ≤ i < r`, all of degree `d = deg O ≥ 2`
(with `O` odd) has at most `⌊d/2⌋` terms. -/
theorem run_length_le {O : P} (hO : IsOdd O) (hd : 2 ≤ O.natDegree) {r : ℕ}
    (hr : ∀ i < r, (T^[i] O).natDegree = O.natDegree) : r ≤ O.natDegree / 2 := by
  obtain ⟨_, hL2, _, hlast⟩ := lem_runs hO hd
  by_contra h
  have := hr _ (lt_of_le_of_lt hL2 (by omega))
  omega

end BinpolyCollatz
