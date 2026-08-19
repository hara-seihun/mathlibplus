import Mathlib

namespace MathlibPlus.Algebra.Claim39331

noncomputable section

private noncomputable def F (a : ℕ) : Polynomial (ZMod 2) :=
  ∑ k ∈ Finset.Icc 1 a, Polynomial.C (a - k + 1 : ZMod 2) * Polynomial.X ^ k

private noncomputable def J (a : ℕ) : Polynomial (ZMod 2) :=
  ∑ k ∈ Finset.range (a + 1), Polynomial.X ^ k

private lemma charTwoPoly : (2 : Polynomial (ZMod 2)) = 0 := by
  ext n
  change (Polynomial.C (2 : ZMod 2)).coeff n = 0
  rw [Polynomial.coeff_C]
  split <;> decide

private lemma addSelf (p : Polynomial (ZMod 2)) : p + p = 0 := by
  rw [← two_mul, charTwoPoly, zero_mul]

private noncomputable def doubleF (a : ℕ) : Polynomial (ZMod 2) :=
  ∑ j ∈ Finset.Icc 1 a, ∑ k ∈ Finset.Icc 1 j, Polynomial.X ^ k

private lemma coeff_sum_finset {R : Type*} [Semiring R] (n : ℕ)
    (s : Finset ℕ) (f : ℕ → Polynomial R) :
    (s.sum f).coeff n = s.sum (fun k => (f k).coeff n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, ih, Polynomial.coeff_add]

private lemma F_eq_doubleF (a : ℕ) : F a = doubleF a := by
  classical
  ext n
  change ((Finset.Icc 1 a).sum
      (fun k => Polynomial.C (a - k + 1 : ZMod 2) * Polynomial.X ^ k)).coeff n = _
  rw [coeff_sum_finset]
  change _ = ((Finset.Icc 1 a).sum
      (fun j => (Finset.Icc 1 j).sum (fun k => Polynomial.X ^ k))).coeff n
  rw [coeff_sum_finset]
  simp_rw [coeff_sum_finset]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hn : n ∈ Finset.Icc 1 a
  · simp only [Finset.mem_Icc] at hn
    simp [mul_ite, Finset.sum_ite_eq, Finset.mem_Icc, hn.1]
    have hfilter : {x ∈ Finset.Icc 1 a | n ≤ x} = Finset.Icc n a := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilter]
    simp
    rw [if_pos hn.2]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · simp only [Finset.mem_Icc] at hn
    simp [mul_ite, Finset.sum_ite_eq, Finset.mem_Icc, hn]
    have hfilter : {x ∈ Finset.Icc 1 a | 1 ≤ n ∧ n ≤ x} = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      simp
      omega
    rw [hfilter]
    simp

private lemma inner (j : ℕ) :
    ((1 : Polynomial (ZMod 2)) + Polynomial.X) *
        (∑ k ∈ Finset.Icc 1 j, Polynomial.X ^ k) =
      Polynomial.X + Polynomial.X ^ (j + 1) := by
  induction j with
  | zero =>
      simp
      exact (addSelf Polynomial.X).symm
  | succ j ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [mul_add, ih]
      rw [show j + 1 + 1 = j + 2 by omega]
      rw [pow_succ]
      ring_nf
      simp [charTwoPoly]

private lemma outer (a : ℕ) :
    ((1 : Polynomial (ZMod 2)) + Polynomial.X) *
        (∑ j ∈ Finset.Icc 1 a,
          (Polynomial.X + Polynomial.X ^ (j + 1))) =
      Polynomial.C (a : ZMod 2) * Polynomial.X +
        Polynomial.C ((a + 1 : ℕ) : ZMod 2) * Polynomial.X ^ 2 +
          Polynomial.X ^ (a + 2) := by
  induction a with
  | zero =>
      simp
      exact (addSelf (Polynomial.X ^ 2)).symm
  | succ a ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [mul_add, ih]
      rw [show a + 1 + 1 = a + 2 by omega]
      rw [pow_succ]
      push_cast
      ring_nf
      have htwo : (2 : ZMod 2) = 0 := by decide
      simp [htwo, charTwoPoly, mul_add, add_assoc, add_left_comm,
        add_comm]
      have hxx : Polynomial.X ^ 2 + Polynomial.X ^ 2 = 0 :=
        addSelf (Polynomial.X ^ 2)
      have hcancel (q : Polynomial (ZMod 2)) :
          Polynomial.X ^ 2 + (Polynomial.X ^ 2 + q) = q := by
        rw [← add_assoc, hxx, zero_add]
      rw [hcancel]
      ring

private lemma F_identity (a : ℕ) :
    ((1 : Polynomial (ZMod 2)) + Polynomial.X) ^ 2 * F a =
      Polynomial.C (a : ZMod 2) * Polynomial.X +
        Polynomial.C ((a + 1 : ℕ) : ZMod 2) * Polynomial.X ^ 2 +
          Polynomial.X ^ (a + 2) := by
  rw [F_eq_doubleF]
  calc
    ((1 : Polynomial (ZMod 2)) + Polynomial.X) ^ 2 * doubleF a =
        ((1 : Polynomial (ZMod 2)) + Polynomial.X) *
          (((1 : Polynomial (ZMod 2)) + Polynomial.X) * doubleF a) := by ring
    _ = ((1 : Polynomial (ZMod 2)) + Polynomial.X) *
        (∑ j ∈ Finset.Icc 1 a,
          (((1 : Polynomial (ZMod 2)) + Polynomial.X) *
            (∑ k ∈ Finset.Icc 1 j, Polynomial.X ^ k))) := by
      congr 1
      rw [← Finset.mul_sum]
      rfl
    _ = ((1 : Polynomial (ZMod 2)) + Polynomial.X) *
        (∑ j ∈ Finset.Icc 1 a,
          (Polynomial.X + Polynomial.X ^ (j + 1))) := by
      congr 2
      funext j
      exact inner j
    _ = _ := outer a

private lemma J_identity (a : ℕ) :
    ((1 : Polynomial (ZMod 2)) + Polynomial.X) * J a =
      1 + Polynomial.X ^ (a + 1) := by
  have hminus : -(1 : Polynomial (ZMod 2)) = 1 := by
    apply (neg_eq_iff_add_eq_zero).2
    calc
      (1 : Polynomial (ZMod 2)) + 1 = 2 := by ring
      _ = 0 := charTwoPoly
  have h := mul_geom_sum (Polynomial.X : Polynomial (ZMod 2)) (a + 1)
  simpa [J, sub_eq_add_neg, hminus, add_comm] using h

/-- The characteristic-two one-arm identities for every positive arm length. -/
theorem oneArmIdentities (a : ℕ) (_ha : 0 < a) :
    (1 + Polynomial.X) ^ 2 * F a =
        Polynomial.C ((a % 2 : ℕ) : ZMod 2) * Polynomial.X +
          Polynomial.C (((a + 1) % 2 : ℕ) : ZMod 2) * Polynomial.X ^ 2 +
            Polynomial.X ^ (a + 2) ∧
      (1 + Polynomial.X) * J a = 1 + Polynomial.X ^ (a + 1) := by
  constructor
  · simpa only [ZMod.natCast_mod] using F_identity a
  · exact J_identity a

end
end MathlibPlus.Algebra.Claim39331
