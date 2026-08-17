import MathlibPlus.Algebra.Claim29919

namespace MathlibPlus.Open.ResearchFormalization.R1061

noncomputable section

abbrev RationalFunction := FractionRing (Polynomial ℚ)

def midpointVariable : RationalFunction :=
  algebraMap (Polynomial ℚ) RationalFunction Polynomial.X

def midpointScalar (δ : ℚ) : RationalFunction :=
  algebraMap ℚ RationalFunction δ

/-- Claim 29926: after removing the common factor `Z - 1`, the endpoint
midpoint completion is the displayed rational function.  The equality is
written in the fraction field of `ℚ[Z]`, so cancellation is an identity of
rational functions rather than a pointwise assertion at the removable node. -/
def claim29926 : Prop :=
  ∀ δ : ℚ, δ ≠ 0 → δ ≠ 1 → δ ≠ 2 →
    MathlibPlus.Algebra.Claim29919.midpointCompletion
        1 2 (midpointScalar δ) midpointVariable =
      (-midpointVariable *
          (midpointScalar δ * midpointVariable + 2 - midpointScalar δ)) /
        ((midpointScalar δ - 2) * midpointVariable - midpointScalar δ)

end
end MathlibPlus.Open.ResearchFormalization.R1061
