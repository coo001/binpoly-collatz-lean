import BinpolyCollatz.Self

namespace BinpolyCollatz
open Polynomial

/-- `dg n i = deg A_{2i+1}` for the odd sequence of `x^n + x + 1`. -/
noncomputable def dg (n i : ℕ) : ℕ := (T^[i] (tri n)).natDegree

lemma dg_rec {n i : ℕ} (hn : 5 ≤ n) (hi : 2 ≤ i) : dg n i = 2 * dg (mSelf n) (i / 2) := by
  obtain ⟨-, -, hself⟩ := prop_self hn
  have h2 : T^[2] (tri n) = T (tri (mSelf n)) ^ 2 := hself
  obtain ⟨-, -, -, hev, hod⟩ := lem_square (isOdd_T (tri (mSelf n)))
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    subst hk; unfold dg
    rw [show 2 * (k' + 1) = 2 * k' + 2 by ring, Function.iterate_add_apply, h2, hev,
      ← Function.iterate_succ_apply, show (2 * k' + 2) / 2 = k'.succ by omega]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    subst hk; unfold dg
    rw [show 2 * (k' + 1) + 1 = 2 * k' + 1 + 2 by ring, Function.iterate_add_apply, h2, hod,
      ← Function.iterate_succ_apply, show (2 * k' + 1 + 2) / 2 = k'.succ by omega]

lemma dg_one_pos {n : ℕ} (hn : 5 ≤ n) : 0 < dg n 1 := by
  obtain ⟨v, -, hv3, hd, -⟩ := natDegree_T_tri (n := n) (by omega)
  unfold dg; simp only [Function.iterate_one]; omega

lemma mSelf_cases (n : ℕ) : (n % 2 = 1 ∧ 2 * mSelf n = n + 1) ∨ (n % 4 = 2 ∧ 2 * mSelf n = n + 2) ∨
    (n % 4 = 0 ∧ 2 * mSelf n = n) := by
  unfold mSelf; split_ifs <;> omega

lemma dg_two_lt_dg_one {n : ℕ} (hn : 9 ≤ n) : dg n 2 < dg n 1 := by
  obtain ⟨hm3, hmn, -⟩ := prop_self (n := n) (by omega)
  have hm5 : 5 ≤ mSelf n := by unfold mSelf; split_ifs <;> omega
  rw [dg_rec (by omega) le_rfl]
  obtain ⟨v, -, -, hd, hv⟩ := natDegree_T_tri (n := n) (by omega)
  obtain ⟨w, hw1, -, hdm, hw⟩ := natDegree_T_tri (n := mSelf n) (by omega)
  unfold dg; simp only [Function.iterate_one, show 2 / 2 = 1 by rfl]
  have hc := mSelf_cases n
  split_ifs at hw hv <;> omega

lemma s_rec {n : ℕ} (hn : 5 ≤ n) :
    Nat.clog 2 (mSelf n) - 2 = Nat.clog 2 n - 2 - 1 ∧ 1 ≤ Nat.clog 2 n - 2 ∧
      (Nat.clog 2 (mSelf n) - 2 ≥ 1 → 5 ≤ mSelf n) := by
  obtain ⟨hk3, hk⟩ := clog_mSelf hn
  refine ⟨by omega, by omega, fun h => ?_⟩
  by_contra h'
  have : Nat.clog 2 (mSelf n) ≤ 2 := (Nat.clog_le_iff_le_pow (by norm_num)).2 (by norm_num; omega)
  omega

lemma blocks_aux {n : ℕ} (hn : 5 ≤ n) :
    (∀ t i, 1 ≤ t → t < Nat.clog 2 n - 2 → 2 ^ t ≤ i → i < 2 ^ (t + 1) → dg n i = dg n (2 ^ t)) ∧
    (∀ t, 1 ≤ t → t + 1 < Nat.clog 2 n - 2 → dg n (2 ^ (t + 1)) < dg n (2 ^ t)) ∧
    (2 ≤ Nat.clog 2 n - 2 → dg n 2 < dg n 1) ∧
    (∀ t, t < Nat.clog 2 n - 2 → 0 < dg n (2 ^ t)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨hm3, hmn, -⟩ := prop_self hn
  obtain ⟨hs, hs1, hm5⟩ := s_rec hn
  set s := Nat.clog 2 n - 2
  set m := mSelf n
  have hpow : ∀ t', (2 : ℕ) ^ (t' + 1) = 2 * 2 ^ t' := fun t' => by ring
  have hpos : ∀ t', 0 < (2 : ℕ) ^ t' := fun t' => by positivity
  have hrec : ∀ t', dg n (2 ^ (t' + 1)) = 2 * dg m (2 ^ t') := fun t' => by
    rw [dg_rec hn (by have := hpos t'; rw [hpow]; omega), hpow, Nat.mul_div_cancel_left _ (by norm_num)]
  have h9 : 2 ≤ s → 9 ≤ n := by
    intro h2
    by_contra h9
    have : Nat.clog 2 n ≤ 3 := (Nat.clog_le_iff_le_pow (by norm_num)).2 (by norm_num; omega)
    omega
  refine ⟨?_, ?_, fun h2 => dg_two_lt_dg_one (h9 h2), ?_⟩
  · intro t i ht1 hts hi1 hi2
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [dg_rec hn (by have := hpos t'; rw [hpow] at hi1; omega), hrec]
    congr 1
    rcases Nat.eq_zero_or_pos t' with h0 | h0
    · subst h0; congr 1; simp at hi1 hi2 ⊢; omega
    · have hm5' := hm5 (by omega)
      rw [hpow, hpow] at hi2; rw [hpow] at hi1
      exact (ih m hmn hm5').1 t' (i / 2) h0 (by omega) (by omega) (by rw [hpow]; omega)
  · intro t ht1 hts
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [hrec, hrec]
    have hm5' := hm5 (by omega)
    rcases Nat.eq_zero_or_pos t' with h0 | h0
    · subst h0
      have := (ih m hmn hm5').2.2.1 (by omega)
      simp only [zero_add, pow_one, pow_zero]; omega
    · have := (ih m hmn hm5').2.1 t' h0 (by omega)
      omega
  · intro t hts
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simpa using dg_one_pos hn
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [hrec]
      have hm5' := hm5 (by omega)
      have := (ih m hmn hm5').2.2.2 t' (by omega)
      omega

/-- **Corollary `cor:blocks`** (Theorem A, degree structure). Let `n ≥ 5`, `s = ⌈log₂ n⌉ - 2`,
and `d i = deg A_{2i+1}` for the odd sequence of `x^n + x + 1`. The finite odd sequence has
`2^s + 1` terms, `d 0 = n > d 1 = e_n > 0`, the indices `[2^t, 2^{t+1})` (`1 ≤ t ≤ s-1`) form
blocks of `2^t` terms of a common degree `d (2^t)`, these degrees strictly decrease and stay
positive, `d 2 < e_n` when `s ≥ 2`, and the last term `d (2^s)` has degree `0`. -/
theorem cor_blocks {n : ℕ} (hn : 5 ≤ n) :
    let s := Nat.clog 2 n - 2
    let d := fun i => (oddSeq (X ^ n + X + 1) i).natDegree
    oddLength (X ^ n + X + 1) = 2 ^ s + 1 ∧
    d 0 = n ∧ d 1 < n ∧ 0 < d 1 ∧
    (∀ t i, 1 ≤ t → t < s → 2 ^ t ≤ i → i < 2 ^ (t + 1) → d i = d (2 ^ t)) ∧
    (2 ≤ s → d 2 < d 1) ∧
    (∀ t, 1 ≤ t → t + 1 < s → d (2 ^ (t + 1)) < d (2 ^ t)) ∧
    (∀ t, 1 ≤ t → t < s → 0 < d (2 ^ t)) ∧
    d (2 ^ s) = 0 := by
  intro s d
  have hd : ∀ i, d i = dg n i := fun i => by
    simp only [d, oddSeq, dg]
    rw [show (X ^ n + X + 1 : P) = tri n from rfl, op_eq_self (isOdd_tri (by omega))]
  obtain ⟨hA, hB, hC, hD⟩ := blocks_aux hn
  simp only [hd]
  refine ⟨thm_tri (by omega), ?_, ?_, dg_one_pos hn, hA, hC, hB, fun t _ ht => hD t ht, ?_⟩
  · simp [dg]; exact natDegree_tri (by omega)
  · obtain ⟨v, hv1, -, hdeg, -⟩ := natDegree_T_tri (n := n) (by omega)
    simp only [dg, Function.iterate_one]; omega
  · have := (sigma_spec (isOdd_tri (n := n) (by omega))).1
    rw [sigma_tri (by omega)] at this
    simp only [dg, s]; rw [this, natDegree_one]

end BinpolyCollatz
