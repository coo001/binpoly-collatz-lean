import Mathlib

/-!
# Binary-polynomial Collatz variant: definitions and the `op` API

Faithful to the manuscript (choi_binary_polynomial_collatz.tex, lines 44-52):
* `P = 𝔽₂[x]`, `M = x^2+x+1`, `y = x(x+1)`;
* `A` odd iff `A(0) = A(1) = 1`;
* `op A` = `A` with all factors `x = X - C 0` and `x+1 = X - C 1` removed;
* `T O = op (1 + M * O)`;
* the odd sequence `A₁ = op A`, `A_{2k+1} = T^k (op A)`, stopped at the first `1`.
-/

namespace BinpolyCollatz
open Polynomial

/-- `P = 𝔽₂[x]` (notation, so that tactics see the literal type `(ZMod 2)[X]`). -/
scoped notation "P" => Polynomial (ZMod 2)

noncomputable def M : P := X ^ 2 + X + 1
noncomputable def y : P := X * (X + 1)

/-- `A` is odd iff `A(0) = A(1) = 1` (equivalently `gcd(A, y) = 1`; this forces `A ≠ 0`). -/
def IsOdd (A : P) : Prop := A.eval 0 = 1 ∧ A.eval 1 = 1

/-- `op A`: `A` with all factors `x` (= `X - C 0`) and `x+1` (= `X - C 1`) removed. -/
noncomputable def op (A : P) : P :=
  A /ₘ ((X - C 0) ^ A.rootMultiplicity 0 * (X - C 1) ^ A.rootMultiplicity 1)

/-- The Collatz-type map `T(O) = op(1 + M O)`. -/
noncomputable def T (O : P) : P := op (1 + M * O)

/-- The odd-indexed terms of the (unstopped) odd sequence: `oddSeq A k = A_{2k+1} = T^k(op A)`. -/
noncomputable def oddSeq (A : P) (k : ℕ) : P := T^[k] (op A)

open Classical in
/-- `σ(O)`: the number of applications of `T` needed to reach `1`
(the least `k` with `T^k O = 1`; junk value `0` if no such `k` exists,
which never happens for odd `O`, see `exists_iterate_eq_one`). -/
noncomputable def sigma (O : P) : ℕ :=
  if h : ∃ k, T^[k] O = 1 then Nat.find h else 0

/-- Length of the odd sequence `A₁, A₃, …` stopped at the first occurrence of `1`. -/
noncomputable def oddLength (A : P) : ℕ := sigma (op A) + 1

/-! ### Basic facts in `𝔽₂` -/

lemma zmod2_eq_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

lemma two_eq_zero_P : (2 : P) = 0 := CharTwo.two_eq_zero

@[simp] lemma X_sub_C_zero : (X - C 0 : P) = X := by simp
@[simp] lemma X_sub_C_one : (X - C 1 : P) = X + 1 := by
  rw [map_one, CharTwo.sub_eq_add]

lemma M_eq : M = X ^ 2 + X + 1 := rfl
lemma y_eq : y = X * (X + 1) := rfl

@[simp] lemma eval_zero_M : M.eval 0 = 1 := by simp [M]
@[simp] lemma eval_one_M : M.eval 1 = 1 := by simp [M]; decide
@[simp] lemma eval_zero_y : y.eval 0 = 0 := by simp [y]
@[simp] lemma eval_one_y : y.eval 1 = 0 := by simp [y]; decide

lemma one_add_M : (1 : P) + M = y := by
  rw [M, y]; linear_combination two_eq_zero_P

lemma M_add_one : M + 1 = y := by rw [add_comm]; exact one_add_M

lemma monic_M : M.Monic := by
  unfold M; monicity!

lemma natDegree_M : M.natDegree = 2 := by
  unfold M; compute_degree!

lemma M_ne_zero : M ≠ 0 := monic_M.ne_zero

lemma natDegree_y : y.natDegree = 2 := by
  unfold y; compute_degree!

lemma monic_y : y.Monic := by unfold y; monicity!

lemma y_ne_zero : y ≠ 0 := monic_y.ne_zero

/-! ### Oddness -/

lemma isOdd_iff_not_isRoot {A : P} : IsOdd A ↔ ¬ A.IsRoot 0 ∧ ¬ A.IsRoot 1 := by
  unfold IsOdd IsRoot
  constructor
  · rintro ⟨h0, h1⟩; simp [h0, h1]
  · rintro ⟨h0, h1⟩; exact ⟨zmod2_eq_one h0, zmod2_eq_one h1⟩

lemma IsOdd.ne_zero {A : P} (h : IsOdd A) : A ≠ 0 := by
  rintro rfl; simp [IsOdd] at h

lemma isOdd_one : IsOdd 1 := by simp [IsOdd]

lemma IsOdd.mul {A B : P} (hA : IsOdd A) (hB : IsOdd B) : IsOdd (A * B) := by
  simp [IsOdd, eval_mul, hA.1, hA.2, hB.1, hB.2]

lemma IsOdd.pow {A : P} (hA : IsOdd A) (n : ℕ) : IsOdd (A ^ n) := by
  simp [IsOdd, eval_pow, hA.1, hA.2]

/-! ### `op` -/

lemma isCoprime_X_X1 : IsCoprime (X - C 0 : P) (X - C 1) :=
  isCoprime_X_sub_C_of_isUnit_sub (by simp)

lemma monic_D (a b : ℕ) : ((X - C 0 : P) ^ a * (X - C 1) ^ b).Monic :=
  ((monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)

lemma rm_D_mul {a b : ℕ} {B : P} (hB : IsOdd B) :
    ((X - C 0 : P) ^ a * (X - C 1) ^ b * B).rootMultiplicity 0 = a ∧
    ((X - C 0 : P) ^ a * (X - C 1) ^ b * B).rootMultiplicity 1 = b := by
  have hB' := isOdd_iff_not_isRoot.1 hB
  have hne : ((X - C 0 : P) ^ a * (X - C 1) ^ b * B) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hB.ne_zero <;>
      exact pow_ne_zero _ (X_sub_C_ne_zero _)
  have hne2 : ((X - C 0 : P) ^ a * (X - C 1) ^ b) ≠ 0 := left_ne_zero_of_mul hne
  rw [rootMultiplicity_mul hne, rootMultiplicity_mul hne2, rootMultiplicity_mul hne,
    rootMultiplicity_mul hne2, rootMultiplicity_X_sub_C_pow, rootMultiplicity_X_sub_C_pow,
    rootMultiplicity_eq_zero hB'.1, rootMultiplicity_eq_zero hB'.2]
  have h01 : ∀ n : ℕ, rootMultiplicity (0 : ZMod 2) ((X - C 1 : P) ^ n) = 0 := fun n =>
    rootMultiplicity_eq_zero (by simp [IsRoot])
  have h10 : ∀ n : ℕ, rootMultiplicity (1 : ZMod 2) ((X - C 0 : P) ^ n) = 0 := fun n =>
    rootMultiplicity_eq_zero (by simp [IsRoot])
  simp

/-- Uniqueness: if `A = x^a (x+1)^b B` with `B` odd, then `op A = B`. -/
lemma op_of_eq {a b : ℕ} {B : P} (hB : IsOdd B) :
    op ((X - C 0 : P) ^ a * (X - C 1) ^ b * B) = B := by
  obtain ⟨h0, h1⟩ := rm_D_mul (a := a) (b := b) hB
  unfold op; rw [h0, h1, mul_divByMonic_cancel_left _ (monic_D a b)]

lemma op_spec {A : P} (hA : A ≠ 0) :
    A = (X - C 0) ^ A.rootMultiplicity 0 * (X - C 1) ^ A.rootMultiplicity 1 * op A := by
  have hdvd : (X - C 0 : P) ^ A.rootMultiplicity 0 * (X - C 1) ^ A.rootMultiplicity 1 ∣ A :=
    (isCoprime_X_X1.pow).mul_dvd (pow_rootMultiplicity_dvd _ _) (pow_rootMultiplicity_dvd _ _)
  have h := modByMonic_add_div A ((X - C 0 : P) ^ A.rootMultiplicity 0 * (X - C 1) ^ A.rootMultiplicity 1)
  rw [(modByMonic_eq_zero_iff_dvd (monic_D _ _)).2 hdvd, zero_add] at h
  exact h.symm

lemma op_isOdd {A : P} (hA : A ≠ 0) : IsOdd (op A) := by
  have hspec := op_spec hA
  have hne : op A ≠ 0 := by
    intro h; rw [h, mul_zero] at hspec; exact hA hspec
  have hne' : (X - C 0 : P) ^ A.rootMultiplicity 0 * (X - C 1) ^ A.rootMultiplicity 1 * op A ≠ 0 :=
    hspec ▸ hA
  have hne2 := left_ne_zero_of_mul hne'
  have e0 := congrArg (rootMultiplicity (0 : ZMod 2)) hspec
  have e1 := congrArg (rootMultiplicity (1 : ZMod 2)) hspec
  have h01 : ∀ n : ℕ, rootMultiplicity (0 : ZMod 2) ((X - C 1 : P) ^ n) = 0 := fun n =>
    rootMultiplicity_eq_zero (by simp [IsRoot])
  have h10 : ∀ n : ℕ, rootMultiplicity (1 : ZMod 2) ((X - C 0 : P) ^ n) = 0 := fun n =>
    rootMultiplicity_eq_zero (by simp [IsRoot])
  rw [rootMultiplicity_mul hne', rootMultiplicity_mul hne2, rootMultiplicity_X_sub_C_pow, h01] at e0
  rw [rootMultiplicity_mul hne', rootMultiplicity_mul hne2, rootMultiplicity_X_sub_C_pow, h10] at e1
  rw [isOdd_iff_not_isRoot]
  constructor
  · intro hr
    have := (rootMultiplicity_pos hne).2 hr
    omega
  · intro hr
    have := (rootMultiplicity_pos hne).2 hr
    omega

lemma op_eq_self {B : P} (hB : IsOdd B) : op B = B := by
  simpa using op_of_eq (a := 0) (b := 0) hB

lemma op_one : op 1 = 1 := op_eq_self isOdd_one

lemma op_mul {A B : P} (hA : A ≠ 0) (hB : B ≠ 0) : op (A * B) = op A * op B := by
  conv_lhs => rw [op_spec hA, op_spec hB]
  rw [show ∀ a b c d e f : P, a * b * c * (d * e * f) = (a * d) * (b * e) * (c * f) by
    intros; ring, ← pow_add, ← pow_add]
  exact op_of_eq ((op_isOdd hA).mul (op_isOdd hB))

lemma op_pow {A : P} (hA : A ≠ 0) (n : ℕ) : op (A ^ n) = op A ^ n := by
  induction n with
  | zero => simp [op_one]
  | succ n ih => rw [pow_succ, op_mul (pow_ne_zero _ hA) hA, ih, pow_succ]

lemma op_X_pow_mul {a : ℕ} {B : P} (hB : B ≠ 0) : op (X ^ a * B) = op B := by
  rw [op_mul (pow_ne_zero _ X_ne_zero) hB]
  have : op (X ^ a : P) = 1 := by
    have := op_of_eq (a := a) (b := 0) isOdd_one
    rwa [pow_zero, mul_one, mul_one, X_sub_C_zero] at this
  rw [this, one_mul]

lemma op_X1_pow_mul {b : ℕ} {B : P} (hB : B ≠ 0) : op ((X + 1) ^ b * B) = op B := by
  have hX1 : (X + 1 : P) ≠ 0 := by rw [← X_sub_C_one]; exact X_sub_C_ne_zero _
  rw [op_mul (pow_ne_zero _ hX1) hB]
  have : op ((X + 1) ^ b : P) = 1 := by
    have := op_of_eq (a := 0) (b := b) isOdd_one
    rwa [pow_zero, one_mul, mul_one, X_sub_C_one] at this
  rw [this, one_mul]

lemma op_y_mul {B : P} (hB : B ≠ 0) : op (y * B) = op B := by
  have hX1 : (X + 1 : P) ≠ 0 := by rw [← X_sub_C_one]; exact X_sub_C_ne_zero _
  have e : y * B = X ^ 1 * ((X + 1) ^ 1 * B) := by rw [y]; ring
  rw [e, op_X_pow_mul (mul_ne_zero (pow_ne_zero _ hX1) hB), op_X1_pow_mul hB]

lemma natDegree_op {A : P} (hA : A ≠ 0) :
    A.natDegree = A.rootMultiplicity 0 + A.rootMultiplicity 1 + (op A).natDegree := by
  have hne : op A ≠ 0 := (op_isOdd hA).ne_zero
  conv_lhs => rw [op_spec hA]
  rw [natDegree_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
      (pow_ne_zero _ (X_sub_C_ne_zero _))) hne,
    natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C]
  ring

lemma natDegree_op_le (A : P) : (op A).natDegree ≤ A.natDegree := by
  by_cases hA : A = 0
  · subst hA; simp [op]
  · rw [natDegree_op hA]; omega

lemma natDegree_op_lt {A : P} (hA : A ≠ 0) (h : ¬ IsOdd A) : (op A).natDegree < A.natDegree := by
  rw [natDegree_op hA]
  rw [isOdd_iff_not_isRoot, not_and_or, not_not, not_not] at h
  rcases h with h | h
  · have := (rootMultiplicity_pos hA).2 h; omega
  · have := (rootMultiplicity_pos hA).2 h; omega

end BinpolyCollatz
