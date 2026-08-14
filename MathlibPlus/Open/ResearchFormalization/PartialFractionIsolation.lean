import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-- A nonconstant affine polynomial over a field. -/
def NonconstantAffinePolynomial {K : Type*} [Field K] (Q : Polynomial K) : Prop :=
  Q.natDegree = 1

/-- The roots of the displayed affine polynomials are pairwise distinct. -/
def PairwiseDistinctPolynomialRoots {K : Type*} [Field K] {s : ℕ}
    (Q : Fin s → Polynomial K) : Prop :=
  ∀ ⦃i j : Fin s⦄, i ≠ j →
    ∀ ⦃x y : K⦄,
      Polynomial.eval x (Q i) = 0 →
      Polynomial.eval y (Q j) = 0 →
      x ≠ y

/-- Partial-fraction isolation for a finite family of affine denominators. -/
def partialFractionIsolationAffine : Prop :=
  ∀ {K : Type*} [Field K] (s : ℕ)
    (Q : Fin s → Polynomial K) (c : Fin s → K),
    (∀ i, NonconstantAffinePolynomial (Q i)) →
    PairwiseDistinctPolynomialRoots Q →
    (∑ i : Fin s,
      (algebraMap K (FractionRing (Polynomial K)) (c i)) /
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)) (Q i))) = 0 →
    ∀ i, c i = 0

end MathlibPlus.Open.ResearchFormalization
