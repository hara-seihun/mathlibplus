import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators
open MvPolynomial
noncomputable section

abbrev SourceArmPolynomial (R : Type*) [CommSemiring R] :=
  MvPolynomial (Fin 3) R

def sourceArmPermutationAction {R : Type*} [CommRing R]
    (π : Equiv.Perm (Fin 3)) (f : SourceArmPolynomial R) : SourceArmPolynomial R :=
  MvPolynomial.rename π f

def sourceArmAlternator {R : Type*} [CommRing R]
    (f : SourceArmPolynomial R) : SourceArmPolynomial R :=
  ∑ π : Equiv.Perm (Fin 3),
    ((π.sign : ℤ) : R) • sourceArmPermutationAction π f

def sourceArmVandermonde {R : Type*} [CommRing R] : SourceArmPolynomial R :=
  (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)

/-- Claim 5373: alternation has sign-representation image and extracts the Vandermonde. -/
def alternatingProjectionAndVandermonde {R : Type*} [CommRing R] : Prop :=
  (∀ (f : SourceArmPolynomial R) (π : Equiv.Perm (Fin 3)),
    sourceArmPermutationAction π (sourceArmAlternator f) =
      ((π.sign : ℤ) : R) • sourceArmAlternator f) ∧
  (∀ f : SourceArmPolynomial R,
    ∃ q : SourceArmPolynomial R,
      sourceArmAlternator f = sourceArmVandermonde * q)

end
end MathlibPlus.Open.Research
