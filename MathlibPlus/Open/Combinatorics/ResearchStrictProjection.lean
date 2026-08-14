import Mathlib

namespace MathlibPlus.Open.ResearchStrictProjection

open scoped BigOperators

noncomputable section

/-- A component-partition monomial has a part larger than `d` when one of the
variables occurring in its exponent has index larger than `d`. -/
def hasPartAbove (d : ℕ) (m : ℕ →₀ ℕ) : Prop :=
  ∃ i ∈ m.support, d < i

/-- The strict-large-component projection, written by the coefficientwise
monomial decomposition of an MvPolynomial. -/
def strictLargeComponentProjection {R : Type*} [CommSemiring R]
    (d : ℕ) (p : MvPolynomial ℕ R) : MvPolynomial ℕ R := by
  classical
  exact (p.support.filter (hasPartAbove d)).sum
    (fun m => MvPolynomial.monomial m (MvPolynomial.coeff m p))

/-- R-4994: on a homogeneous component-partition polynomial of weight `n-d`,
the strict-large-component projection keeps precisely the monomials with a
part strictly larger than `d`. -/
def claim55007 : Prop := by
  classical
  exact ∀ (R : Type*) [CommRing R] (n d : ℕ) (p : MvPolynomial ℕ R),
    (∀ m ∈ p.support, m.sum (fun i e => i * e) = n - d) →
    ∀ m : ℕ →₀ ℕ,
      MvPolynomial.coeff m (strictLargeComponentProjection d p) =
        if hasPartAbove d m then MvPolynomial.coeff m p else 0

end
end MathlibPlus.Open.ResearchStrictProjection
