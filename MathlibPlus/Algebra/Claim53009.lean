import Mathlib

namespace MathlibPlus.Algebra.Claim53009

open scoped BigOperators Polynomial

/-- The coefficient functional associated with a sequence of host weights. -/
noncomputable def A {R : Type*} [CommSemiring R]
    (x : ℕ → R) (s : ℕ) (P : R[X]) : R :=
  P.sum (fun a c => x (a + s) * c)

/-- The complete two-host coefficient pairing.  The first summand is the
product of the two one-host responses, while the second is the response of
the coefficient convolution at the sum of the two exponents. -/
noncomputable def B {R : Type*} [CommSemiring R]
    (x : ℕ → R) (P Q : R[X]) : R :=
  ∑ a ∈ P.support, ∑ b ∈ Q.support,
    (x (a + 1) * x (b + 1) + x (a + b + 2)) * P.coeff a * Q.coeff b

lemma A_one_mul {R : Type*} [CommSemiring R]
    (x : ℕ → R) (P Q : R[X]) :
    A x 1 P * A x 1 Q =
      ∑ a ∈ P.support, ∑ b ∈ Q.support,
        (x (a + 1) * x (b + 1)) * P.coeff a * Q.coeff b := by
  simp only [A, Polynomial.sum_def, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma A_two_mul {R : Type*} [CommSemiring R]
    (x : ℕ → R) (P Q : R[X]) :
    A x 2 (P * Q) =
      ∑ a ∈ P.support, ∑ b ∈ Q.support,
        x (a + b + 2) * P.coeff a * Q.coeff b := by
  have hadd : ∀ U V : R[X], A x 2 (U + V) = A x 2 U + A x 2 V := by
    intro U V
    simp only [A]
    rw [Polynomial.sum_add_index]
    · intro i
      exact mul_zero _
    · intro i a b
      simp [mul_add]
  have hsum : ∀ (t : Finset ℕ) (F : ℕ → R[X]),
      A x 2 (∑ i ∈ t, F i) = ∑ i ∈ t, A x 2 (F i) := by
    intro t F
    induction t using Finset.induction_on with
    | empty => simp [A]
    | @insert i t hi ih =>
        rw [Finset.sum_insert hi, hadd, ih]
        simp [Finset.sum_insert, hi]
  have hmono : ∀ (n : ℕ) (r : R),
      A x 2 (Polynomial.monomial n r) = x (n + 2) * r := by
    intro n r
    simp [A]
  rw [Polynomial.mul_eq_sum_sum]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Polynomial.sum_def]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hmono]
  ring

/-- Coefficientwise differentiation in the host-variable ring. -/
noncomputable def coefficientDeriv {R : Type*} [CommSemiring R]
    (D : R → R) (P : R[X]) : R[X] :=
  ∑ a ∈ P.support, Polynomial.monomial a (D (P.coeff a))

/-- Claim 53009's response-row derivative identity, stated for any derivation
whose coordinate values on the host weights are the Kronecker delta. -/
theorem response_row_derivative {R : Type*} [CommSemiring R]
    (x : ℕ → R) (D : R → R) (k s : ℕ) (P : R[X])
    (hDzero : D 0 = 0)
    (hDadd : ∀ u v : R, D (u + v) = D u + D v)
    (hDmul : ∀ u v : R, D (u * v) = D u * v + u * D v)
    (hDx : ∀ n : ℕ, D (x n) = if n = k then 1 else 0) :
    D (A x s P) =
      (if s ≤ k then P.coeff (k - s) else 0) +
        A x s (coefficientDeriv D P) := by
  have hAadd : ∀ U V : R[X], A x s (U + V) = A x s U + A x s V := by
    intro U V
    simp only [A]
    rw [Polynomial.sum_add_index]
    · intro i
      exact mul_zero _
    · intro i a b
      simp [mul_add]
  have hAsum : ∀ (t : Finset ℕ) (f : ℕ → R[X]),
      A x s (∑ i ∈ t, f i) = ∑ i ∈ t, A x s (f i) := by
    intro t f
    induction t using Finset.induction_on with
    | empty => simp [A]
    | @insert i t hi ih =>
        rw [Finset.sum_insert hi, hAadd, ih]
        simp [Finset.sum_insert, hi]
  have hsum : ∀ (t : Finset ℕ) (f : ℕ → R),
      D (∑ i ∈ t, f i) = ∑ i ∈ t, D (f i) := by
    intro t f
    induction t using Finset.induction_on with
    | empty => simp [hDzero]
    | @insert i t hi ih =>
        rw [Finset.sum_insert hi, hDadd, ih, Finset.sum_insert hi]
  have hcoef :
      A x s (coefficientDeriv D P) =
        ∑ a ∈ P.support, x (a + s) * D (P.coeff a) := by
    rw [coefficientDeriv, hAsum]
    apply Finset.sum_congr rfl
    intro a ha
    simp [A]
  have hfirst :
      (∑ a ∈ P.support, (if a + s = k then 1 else 0) * P.coeff a) =
        (if s ≤ k then P.coeff (k - s) else 0) := by
    by_cases hsk : s ≤ k
    · have hcond : ∀ a : ℕ, (a + s = k) ↔ a = k - s := by
        intro a
        omega
      simp_rw [hcond]
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp [hsk, eq_comm]
    · have hzero : ∀ a : ℕ, a + s ≠ k := by
        intro a ha
        omega
      simp [hzero, hsk]
  calc
    D (A x s P) = D (∑ a ∈ P.support, x (a + s) * P.coeff a) := by
      rfl
    _ = ∑ a ∈ P.support, D (x (a + s) * P.coeff a) := hsum _ _
    _ = ∑ a ∈ P.support,
        (D (x (a + s)) * P.coeff a + x (a + s) * D (P.coeff a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrArg (fun z => z) (hDmul _ _)
    _ = (if s ≤ k then P.coeff (k - s) else 0) +
        A x s (coefficientDeriv D P) := by
      simp only [hDx]
      rw [Finset.sum_add_distrib, hfirst]
      exact congrArg
        (fun z => (if s ≤ k then P.coeff (k - s) else 0) + z) hcoef.symm

/-- Claim 53009's complete two-host identity. -/
theorem complete_two_host_identity {R : Type*} [CommSemiring R]
    (x : ℕ → R) (P Q : R[X]) :
    B x P Q = A x 1 P * A x 1 Q + A x 2 (P * Q) := by
  rw [A_one_mul, A_two_mul]
  simp only [B]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  ring

end MathlibPlus.Algebra.Claim53009
