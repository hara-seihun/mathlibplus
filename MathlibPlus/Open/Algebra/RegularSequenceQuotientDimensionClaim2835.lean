import MathlibPlus.Open.Algebra.QuotientEmbeddingInterval

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Algebra.RegularSequenceQuotientDimensionClaim2835

abbrev symmetricRing :=
  MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.symmetricRing
abbrev ambientRing :=
  MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.ambientRing

noncomputable def powerSumGenerator (j d : ℕ) (i : Fin j) : symmetricRing j :=
  MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.powerSum j
    (d + i.1 + 1)

def elementaryCoordinateWeight {j : ℕ} (i : Fin j) : ℕ :=
  i.1 + 1

noncomputable def powerSumPrefixIdeal (j d : ℕ) (i : Fin j) :
    Ideal (symmetricRing j) :=
  Ideal.span {a | ∃ k : Fin j, k.1 < i.1 ∧ a = powerSumGenerator j d k}

def orderedRegularSequence (j d : ℕ) : Prop :=
  ∀ i : Fin j,
    IsRegular
      (Ideal.Quotient.mk (powerSumPrefixIdeal j d i)
        (powerSumGenerator j d i))

def homogeneousSystemOfParameters (j d : ℕ) : Prop :=
  (∀ i : Fin j,
    MvPolynomial.IsHomogeneous
      ((powerSumGenerator j d i : symmetricRing j) : ambientRing j)
      (d + elementaryCoordinateWeight i)) ∧
    Module.Finite ℚ
      ((symmetricRing j) ⧸
        MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j d)

def quotientArtinianCompleteIntersection (j d : ℕ) : Prop :=
  orderedRegularSequence j d ∧
    IsArtinian
      ((symmetricRing j) ⧸
        MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j d)
      ((symmetricRing j) ⧸
        MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j d)

def claim2835 : Prop :=
  ∀ j d : ℕ,
    homogeneousSystemOfParameters j d ∧
      quotientArtinianCompleteIntersection j d ∧
      Module.finrank ℚ
          ((symmetricRing j) ⧸
            MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j d) =
        Nat.choose (d + j) j ∧
      ((Module.finrank ℚ
          ((symmetricRing j) ⧸
            MathlibPlus.Open.Algebra.QuotientEmbeddingInterval.consecutivePowerSumIdeal j d) : ℕ) : ℚ) =
        ∏ i : Fin j,
          ((d + elementaryCoordinateWeight i : ℕ) : ℚ) /
            ((elementaryCoordinateWeight i : ℕ) : ℚ)

end MathlibPlus.Open.Algebra.RegularSequenceQuotientDimensionClaim2835

end
