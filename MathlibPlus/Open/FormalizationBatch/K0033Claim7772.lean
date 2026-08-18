import MathlibPlus.Open.FormalizationBatch.Claims7774And7880
import MathlibPlus.Open.RepresentationTheory.PairedModuleQuotientRepresentation

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch.K0033Claim7772

open MathlibPlus.Open.FormalizationBatch

noncomputable section

/-- Complex-valued rows invariant under the diagonal subgroup H. -/
def relativeHInvariantComplex7772 (f : RelativeGroup → ℂ) : Prop :=
  ∀ g h, h ∈ relativeH → f (g + h) = f g

/-- The four Fourier coefficients in the concrete ordered character basis. -/
def relativeFourierCoefficient7772
    (f : RelativeGroup → ℂ) (i : Fin 4) : ℂ :=
  ∑ g : RelativeGroup,
    f g * star (relativeCharacter i g)

/-- Claim 7772: the diagonal H-Reynolds projector keeps exactly the trivial
and relative characters, and every H-invariant row has support in those two
characters. -/
def exactQuotientCharacterSupport_claim7772 : Prop :=
  relativeFourierMultiplier 1 0 = 1 ∧
    relativeFourierMultiplier 1 1 = 0 ∧
    relativeFourierMultiplier 1 2 = 0 ∧
    relativeFourierMultiplier 1 3 = 1 ∧
    (∀ (f : RelativeGroup → ℂ),
      relativeHInvariantComplex7772 f →
        ∀ i : Fin 4,
          relativeFourierCoefficient7772 f i ≠ 0 →
            i = 0 ∨ i = 3)

end

end MathlibPlus.Open.FormalizationBatch.K0033Claim7772
