import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.OddAntisymmetricPairCancellation

/-- Claim 6196: on every odd antidiagonal, an integer-valued antisymmetric
weight cancels after multiplication by a commutative coefficient sequence. -/
def oddAntisymmetricPairCancellation : Prop :=
  ∀ (R : Type*) [CommRing R] (N : ℕ),
    Odd N →
    ∀ (W : ℕ → ℕ → ℤ),
      (∀ i j : ℕ, W j i = -W i j) →
      ∀ (u : ℕ → R),
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N,
            (W ij.1 ij.2 : R) * u ij.1 * u ij.2 = 0

end MathlibPlus.Algebra.OddAntisymmetricPairCancellation
