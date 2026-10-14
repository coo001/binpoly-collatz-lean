import BinpolyCollatz.Square

namespace BinpolyCollatz
open Polynomial

/-- `F_j = x^j M + 1` (for `j = 0` this is `M + 1 = y`, matching the paper's `F_0 = y`). -/
noncomputable def F (j : ℕ) : P := X ^ j * M + 1

lemma F_zero : F 0 = y := by rw [F, pow_zero, one_mul, M_add_one]

lemma natDegree_F (j : ℕ) : (F j).natDegree = j + 2 := by
  rw [F, add_comm, natDegree_one_add] <;>
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) M_ne_zero, natDegree_X_pow, natDegree_M] <;> omega

lemma F_ne_zero (j : ℕ) : F j ≠ 0 := by
  intro h; have := natDegree_F j; rw [h] at this; simp at this

lemma eval_zero_F {j : ℕ} (hj : 1 ≤ j) : (F j).eval 0 = 1 := by
  have : j ≠ 0 := by omega
  simp [F, this]

/-- The trinomial `x^n + x + 1`. -/
noncomputable def tri (n : ℕ) : P := X ^ n + X + 1

lemma isOdd_tri {n : ℕ} (hn : 1 ≤ n) : IsOdd (tri n) := by
  have : n ≠ 0 := by omega
  refine ⟨by simp [tri, this], ?_⟩
  simp [tri]; decide

lemma natDegree_tri {n : ℕ} (hn : 2 ≤ n) : (tri n).natDegree = n := by
  unfold tri
  have h1 : (X + 1 : P).natDegree ≤ 1 := by compute_degree
  have h2 : (X + 1 : P).natDegree < (X ^ n : P).natDegree := by rw [natDegree_X_pow]; omega
  rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt h2, natDegree_X_pow]

lemma tri_ne_one {n : ℕ} (hn : 2 ≤ n) : tri n ≠ 1 := by
  intro h; have := natDegree_tri hn; rw [h] at this; simp at this; omega

/-- **Lemma `lem:Tri`.** For `n ≥ 3`, `T(x^n + x + 1) = op(F_{n-3})`. -/
theorem lem_Tri {n : ℕ} (hn : 3 ≤ n) : T (X ^ n + X + 1) = op (F (n - 3)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  rw [Nat.add_sub_cancel, T,
    show 1 + M * (X ^ (j + 3) + X + 1) = X ^ 3 * F j by rw [F, M]; ring2,
    op_X_pow_mul (F_ne_zero j)]

/-! ### Lemma `lem:val`: explicit factorizations `F_j = (x+1)^v Q` with `Q(1) = 1` -/

lemma decomp_even (i : ℕ) : ∃ Q : P, Q.eval 1 = 1 ∧ F (2 * i) = (X + 1) * Q := by
  obtain ⟨R, hR⟩ := sub_dvd_pow_sub_pow ((X : P) ^ 2) 1 i
  refine ⟨1 + (X + 1) + (X + 1) * R * M, by simp [zmod2_one_add_one], ?_⟩
  rw [F, M] at *
  linear_combination (norm := ring2) (X ^ 2 + X + 1) * hR

lemma decomp_three (i : ℕ) : ∃ Q : P, Q.eval 1 = 1 ∧ F (4 * i + 3) = (X + 1) ^ 2 * Q := by
  obtain ⟨R, hR⟩ := sub_dvd_pow_sub_pow ((X : P) ^ 4) 1 i
  refine ⟨1 + (X + 1) + (X + 1) ^ 3 +
    (X + 1) ^ 2 * R * (1 + (X + 1) ^ 2 + (X + 1) ^ 3 + (X + 1) ^ 5), by simp [zmod2_one_add_one], ?_⟩
  rw [F, M]
  linear_combination (norm := ring2) (X ^ 3 * (X ^ 2 + X + 1)) * hR

lemma decomp_one (i : ℕ) : ∃ Q : P, Q.eval 1 = 1 ∧ F (4 * i + 1) = (X + 1) ^ 3 * Q := by
  obtain ⟨R, hR⟩ := sub_dvd_pow_sub_pow ((X : P) ^ 4) 1 i
  refine ⟨1 + (X + 1) * R + (X + 1) ^ 4 * R, by simp [zmod2_one_add_one], ?_⟩
  rw [F, M]
  linear_combination (norm := ring2) (X * (X ^ 2 + X + 1)) * hR

lemma rm1_of_eq {v : ℕ} {Q : P} (hQ : Q.eval 1 ≠ 0) : ((X + 1) ^ v * Q).rootMultiplicity 1 = v := by
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  rw [← X_sub_C_one, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) hQ0),
    rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero (by simpa [IsRoot] using hQ), add_zero]

/-- **Lemma `lem:val`.** For `j ≥ 1`, `v_{x+1}(F_j)` is `1` if `j` is even, `2` if `j ≡ 3 (mod 4)`,
and `3` if `j ≡ 1 (mod 4)`. -/
theorem lem_val (j : ℕ) (_hj : 1 ≤ j) :
    (j % 2 = 0 → (F j).rootMultiplicity 1 = 1) ∧
    (j % 4 = 3 → (F j).rootMultiplicity 1 = 2) ∧
    (j % 4 = 1 → (F j).rootMultiplicity 1 = 3) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨Q, hQ, e⟩ := decomp_even (j / 2)
    rw [show j = 2 * (j / 2) by omega, e, ← pow_one (X + 1 : P), rm1_of_eq (by rw [hQ]; decide)]
  · obtain ⟨Q, hQ, e⟩ := decomp_three (j / 4)
    rw [show j = 4 * (j / 4) + 3 by omega, e, rm1_of_eq (by rw [hQ]; decide)]
  · obtain ⟨Q, hQ, e⟩ := decomp_one (j / 4)
    rw [show j = 4 * (j / 4) + 1 by omega, e, rm1_of_eq (by rw [hQ]; decide)]

end BinpolyCollatz
