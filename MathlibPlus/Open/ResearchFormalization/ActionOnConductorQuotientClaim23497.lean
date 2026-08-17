import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Open.ResearchFormalization.ActionOnConductorQuotientClaim23497

open MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev ScalarA := ScalarRing
abbrev ConductorK : Ideal ScalarA := scalarRingKernelIdeal
abbrev ConductorSquare : Ideal ScalarA := ConductorK * ConductorK
abbrev SquareQuotient := ScalarA ⧸ ConductorSquare

/-- The image of the conductor in `A/K²`, a canonical carrier for `K/K²`. -/
abbrev ConductorLayer : Ideal SquareQuotient :=
  Ideal.map (Ideal.Quotient.mk ConductorSquare) ConductorK

def conductorMultiplication : Prop :=
  ∀ (a : ScalarA), a ∈ ConductorK →
    ∀ (k : ScalarA), k ∈ ConductorK → a * k ∈ ConductorSquare

def actionFactorsThroughConductorQuotient
    {φ : (ScalarA ⧸ ConductorK) ≃+* Polynomial ℚ} : Prop :=
  ∀ (a a' : ScalarA),
    φ (Ideal.Quotient.mk ConductorK a) =
      φ (Ideal.Quotient.mk ConductorK a') →
      ∀ x : ConductorLayer, a • x = a' • x

/-- Claim 23497: the actual conductor ideal acts trivially on the actual
`K/K²` layer, so the scalar action depends only on `A/K`, whose reviewed
conductor presentation identifies it with `ℚ[s]` represented as `Polynomial ℚ`.
-/
def actionOnConductorQuotient_claim23497 : Prop :=
  claim_23495 →
    ∃ φ : (ScalarA ⧸ ConductorK) ≃+* Polynomial ℚ,
      conductorMultiplication ∧
        actionFactorsThroughConductorQuotient (φ := φ)

end
end MathlibPlus.Open.ResearchFormalization.ActionOnConductorQuotientClaim23497
