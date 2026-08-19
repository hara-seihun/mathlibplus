import Mathlib

namespace MathlibPlus.Open.Algebra.Claim24744

/-- Claim 24744: a primitive degree-one polynomial is irreducible over the
fraction field and, by Gauss's lemma, in the cavity UFD itself. -/
def primitiveLinearPolynomialIrreducible_claim24744 : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {p : Polynomial R},
    p.IsPrimitive → p.degree = 1 →
      Irreducible (p.map (algebraMap R (FractionRing R))) ∧
        Irreducible p

end MathlibPlus.Open.Algebra.Claim24744
