import BinpolyCollatz.Runs

namespace BinpolyCollatz
open Polynomial

/-- An odd polynomial of degree `≤ 1` is `1` (no odd polynomial has degree `1`). -/
lemma eq_one_of_isOdd_natDegree_le_one {O : P} (hO : IsOdd O) (h : O.natDegree ≤ 1) : O = 1 := by
  have e := eq_X_add_C_of_natDegree_le_one h
  have h0 := hO.1; have h1 := hO.2
  rw [e] at h0 h1
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add, mul_one] at h0 h1
  have hc1 : O.coeff 1 = 0 := by
    rw [h0] at h1
    have key : ∀ a : ZMod 2, a + 1 = 1 → a = 0 := by decide
    exact key _ h1
  rw [e, hc1, h0]; simp

lemma sq_div_four_step (N N' L : ℕ) (hN' : N' < N) (hL : L ≤ N / 2) :
    L + N' ^ 2 / 4 ≤ N ^ 2 / 4 := by
  have h1 : N' ^ 2 / 4 ≤ (N - 1) ^ 2 / 4 :=
    Nat.div_le_div_right (Nat.pow_le_pow_left (by omega) 2)
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · rcases m with _ | m
    · omega
    · have e1 : (2 * (m + 1) - 1) ^ 2 / 4 = m * m + m := by
        have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [this]; ring_nf; omega
      have e2 : (2 * (m + 1)) ^ 2 / 4 = (m + 1) * (m + 1) := by ring_nf; omega
      have e3 : 2 * (m + 1) / 2 = m + 1 := by omega
      rw [e1] at h1; rw [e2]; rw [e3] at hL; nlinarith
  · have e1 : (2 * m + 1 - 1) ^ 2 / 4 = m * m := by
      have : 2 * m + 1 - 1 = 2 * m := by omega
      rw [this]; ring_nf; omega
    have e2 : (2 * m + 1) ^ 2 / 4 = m * m + m := by ring_nf; omega
    have e3 : (2 * m + 1) / 2 = m := by omega
    rw [e1] at h1; rw [e2]; rw [e3] at hL; omega

/-- Every odd `O` of degree `N` reaches `1` within `⌊N²/4⌋` applications of `T`. -/
theorem exists_iterate_eq_one_le {O : P} (hO : IsOdd O) :
    ∃ k ≤ O.natDegree ^ 2 / 4, T^[k] O = 1 := by
  induction hN : O.natDegree using Nat.strong_induction_on generalizing O with
  | _ N ih =>
    by_cases hN2 : N ≤ 1
    · exact ⟨0, Nat.zero_le _, by
        rw [Function.iterate_zero_apply]; exact eq_one_of_isOdd_natDegree_le_one hO (by omega)⟩
    · have hd : 2 ≤ O.natDegree := by omega
      obtain ⟨_, hL2, _, hlast⟩ := lem_runs hO hd
      set L := min ((O + 1).rootMultiplicity 0) ((O + 1).rootMultiplicity 1)
      obtain ⟨k, hk, hk1⟩ := ih _ (hN ▸ hlast) (isOdd_iterate_T hO L) rfl
      refine ⟨k + L, ?_, by rw [Function.iterate_add_apply, hk1]⟩
      have := sq_div_four_step N _ L (hN ▸ hlast) (hN ▸ hL2)
      omega

theorem exists_iterate_eq_one {O : P} (hO : IsOdd O) : ∃ k, T^[k] O = 1 :=
  let ⟨k, _, hk⟩ := exists_iterate_eq_one_le hO; ⟨k, hk⟩

/-! ### `σ` API -/

lemma sigma_spec {O : P} (hO : IsOdd O) :
    T^[sigma O] O = 1 ∧ ∀ m < sigma O, T^[m] O ≠ 1 := by
  classical
  have h := exists_iterate_eq_one hO
  have hs : sigma O = Nat.find h := by simp only [sigma, h, ↓reduceDIte]
  rw [hs]
  exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

lemma sigma_eq_iff {O : P} (hO : IsOdd O) {n : ℕ} :
    sigma O = n ↔ T^[n] O = 1 ∧ ∀ m < n, T^[m] O ≠ 1 := by
  obtain ⟨h1, h2⟩ := sigma_spec hO
  constructor
  · rintro rfl; exact ⟨h1, h2⟩
  · rintro ⟨h3, h4⟩
    rcases lt_trichotomy (sigma O) n with h | h | h
    · exact absurd h1 (h4 _ h)
    · exact h
    · exact absurd h3 (h2 _ h)

lemma sigma_le {O : P} (hO : IsOdd O) {k : ℕ} (hk : T^[k] O = 1) : sigma O ≤ k := by
  by_contra h; exact (sigma_spec hO).2 k (by omega) hk

lemma lt_sigma {O : P} (hO : IsOdd O) {i : ℕ} (hi : ∀ j ≤ i, T^[j] O ≠ 1) : i < sigma O := by
  by_contra h; exact hi _ (by omega) (sigma_spec hO).1

/-- The finite odd sequence: `oddSeq A k` for `k ≤ σ(op A)` are exactly its terms, the last
being the first occurrence of `1`. -/
theorem oddSeq_spec {A : P} (hA : A ≠ 0) :
    oddSeq A (oddLength A - 1) = 1 ∧ ∀ k < oddLength A - 1, oddSeq A k ≠ 1 := by
  simpa [oddSeq, oddLength] using sigma_spec (op_isOdd hA)

/-- **Theorem `thm:bound`** (Theorem C, second part). If `A ≠ 0` has degree `n`, the odd sequence
of `A` has length at most `⌊n²/4⌋ + 1`. -/
theorem thm_bound {A : P} (hA : A ≠ 0) : oddLength A ≤ A.natDegree ^ 2 / 4 + 1 := by
  have hO := op_isOdd hA
  obtain ⟨k, hk, hk1⟩ := exists_iterate_eq_one_le hO
  have h1 := sigma_le hO hk1
  have h2 : (op A).natDegree ^ 2 / 4 ≤ A.natDegree ^ 2 / 4 :=
    Nat.div_le_div_right (Nat.pow_le_pow_left (natDegree_op_le A) 2)
  unfold oddLength; omega

/-! ### `G(n)` and Theorem `thm:g` -/

/-- `G(n)`: the maximal number of initial terms `A₁, A₃, …` of degree `n` in the finite odd
sequence of an odd polynomial `A` of degree `n`. -/
noncomputable def G (n : ℕ) : ℕ :=
  sSup {r | ∃ A : P, IsOdd A ∧ A.natDegree = n ∧
    ∀ i < r, i < oddLength A ∧ (oddSeq A i).natDegree = n}

/-- Equality witnesses for `thm:g`. -/
lemma witness (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : P, IsOdd A ∧ A.natDegree = n ∧ ∀ i < n / 2, (T^[i] A).natDegree = n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- `A = 1 + y^m`
    have hm : 1 ≤ m := by omega
    refine ⟨1 + y ^ m, ?_, ?_, ?_⟩
    · have : m ≠ 0 := by omega
      simp [IsOdd, eval_pow, this]
    · rw [natDegree_one_add] <;> rw [natDegree_pow, natDegree_y] <;> omega
    · obtain ⟨hdeg, hiter, _⟩ := runs_core (O := 1 + y ^ m) (K := 1) hm one_ne_zero
        (by rw [mul_one]; linear_combination two_eq_zero_P) (by simp)
      intro i hi
      rw [(hiter i (by omega)).2, hdeg]; simp
  · -- `A = 1 + x y^m`
    have hm : 1 ≤ m := by omega
    refine ⟨1 + y ^ m * X, ?_, ?_, ?_⟩
    · have : m ≠ 0 := by omega
      simp [IsOdd, eval_pow, this]
    · rw [natDegree_one_add] <;>
        rw [natDegree_mul (pow_ne_zero _ y_ne_zero) X_ne_zero, natDegree_pow, natDegree_y,
          natDegree_X] <;> omega
    · obtain ⟨hdeg, hiter, _⟩ := runs_core (O := 1 + y ^ m * X) (K := X) hm X_ne_zero
        (by linear_combination two_eq_zero_P) (by simp)
      intro i hi
      rw [(hiter i (by omega)).2, hdeg]; simp

/-- **Theorem `thm:g`** (Theorem C, first part). For `n ≥ 2`, `G(n) = ⌊n/2⌋`. -/
theorem thm_g (n : ℕ) (hn : 2 ≤ n) : G n = n / 2 := by
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨A, hA, hdeg, hrun⟩ := witness n hn
    refine ⟨A, hA, hdeg, fun i hi => ⟨?_, ?_⟩⟩
    · have : i < sigma A := by
        apply lt_sigma hA
        intro j hj h1
        have := hrun j (by omega); rw [h1] at this; simp at this; omega
      unfold oddLength; rw [op_eq_self hA]; omega
    · rw [oddSeq, op_eq_self hA]; exact hrun i hi
  · rintro r ⟨A, hA, hdeg, hrun⟩
    have := run_length_le hA (by omega) (r := r) (fun i hi => by
      have := (hrun i hi).2; rw [oddSeq, op_eq_self hA] at this; rw [this, hdeg])
    omega

end BinpolyCollatz
