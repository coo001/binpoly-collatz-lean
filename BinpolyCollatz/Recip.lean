import BinpolyCollatz.Self

namespace BinpolyCollatz
open Polynomial

lemma clog_succ_eq_log_add_one {n : ℕ} (hn : 1 ≤ n) : Nat.clog 2 (n + 1) = Nat.log 2 n + 1 := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]; omega
  · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]; omega

/-- **Corollary `cor:recip`.** For `n ≥ 2`, `T(x^n + x^{n-1} + 1) = T(x^{n+1} + x + 1)`; the odd
sequence of `x^n + x^{n-1} + 1` has length `2^(⌊log₂ n⌋ - 1) + 1`; its first term has degree `n`
and all later terms coincide with those of the odd sequence of `x^{n+1} + x + 1`. -/
theorem cor_recip {n : ℕ} (hn : 2 ≤ n) :
    T (X ^ n + X ^ (n - 1) + 1) = T (X ^ (n + 1) + X + 1) ∧
    oddLength (X ^ n + X ^ (n - 1) + 1) = 2 ^ (Nat.log 2 n - 1) + 1 ∧
    (oddSeq (X ^ n + X ^ (n - 1) + 1) 0).natDegree = n ∧
    ∀ i, 1 ≤ i → oddSeq (X ^ n + X ^ (n - 1) + 1) i = oddSeq (X ^ (n + 1) + X + 1) i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  set R : P := X ^ (k + 2) + X ^ (k + 1) + 1
  have hRodd : IsOdd R := ⟨by simp [R], by simp [R]; decide⟩
  have hRdeg : R.natDegree = k + 2 := by
    simp only [R]; compute_degree!
  have hT : T R = T (X ^ (k + 2 + 1) + X + 1) := by
    rw [lem_Tri (by omega), show k + 2 + 1 - 3 = k by omega, T,
      show 1 + M * R = y * F k by simp only [R, M, y, F]; ring2, op_y_mul (F_ne_zero k)]
  have htri : (X ^ (k + 2 + 1) + X + 1 : P) = tri (k + 3) := rfl
  have hR1 : R ≠ 1 := by intro h; rw [h] at hRdeg; simp at hRdeg
  have hseq : ∀ i, 1 ≤ i → oddSeq R i = oddSeq (X ^ (k + 2 + 1) + X + 1) i := by
    intro i hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [oddSeq, oddSeq, op_eq_self hRodd, htri, op_eq_self (isOdd_tri (by omega)),
      Function.iterate_succ_apply, Function.iterate_succ_apply, hT, htri]
  refine ⟨hT, ?_, by rw [oddSeq, op_eq_self hRodd]; exact hRdeg, hseq⟩
  rw [oddLength, op_eq_self hRodd, sigma_succ hRodd hR1, hT, htri,
    ← sigma_succ (isOdd_tri (by omega)) (tri_ne_one (by omega)), sigma_tri (by omega),
    show k + 3 = (k + 2) + 1 by rfl, clog_succ_eq_log_add_one (by omega),
    show Nat.log 2 (k + 2) + 1 - 2 = Nat.log 2 (k + 2) - 1 by omega]

end BinpolyCollatz
