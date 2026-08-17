import MathlibPlus.Open.Algebra.QuotientEmbeddingInterval

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Algebra.ConsecutivePowerSumIdealClaims2833

abbrev ambientRing := MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.ambientRing

def truncatedVariableIdeal (j d : ℕ) :
    Ideal (ambientRing j) :=
  Ideal.span (Set.range (fun i : Fin j =>
    (MvPolynomial.X i : ambientRing j) ^ (d + 1)))

def claim2833 : Prop :=
  ∀ j d : ℕ,
    let R := ambientRing j
    let S := MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.symmetricRing j
    let J : Ideal R := truncatedVariableIdeal j d
    let I : Ideal S :=
      MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j d
    (J = Ideal.span (Set.range (fun i : Fin j =>
      (MvPolynomial.X i : R) ^ (d + 1)))) ∧
      (I = Ideal.span (Set.range (fun i : Fin j =>
        MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.powerSum j
          (d + i.1 + 1))))

end MathlibPlus.Open.Algebra.ConsecutivePowerSumIdealClaims2833

end
