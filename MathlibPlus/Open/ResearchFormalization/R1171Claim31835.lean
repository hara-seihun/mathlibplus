import MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837
import MathlibPlus.Open.ResearchFormalization.R1171Claim41590

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim31835

open MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837
open MathlibPlus.Open.ResearchFormalization.R1171Claim41590

noncomputable section

/-- Conjugacy of the two exact regular copies by an element of their actual
    generated image. -/
def actualImageConjugacy (f : FiberFunction) : Prop :=
  ∃ g : Equiv.Perm FiberOmega,
    g ∈ fiberGeneratedImage f ∧
      conjugateSubgroup g fiberTranslations = fiberTarget f

/-- Membership of the shear function in the derivative module plus the full
    affine-function summand. -/
def affineDifferenceMembership (f : FiberFunction) : Prop :=
  ∃ h : FiberFunction, h ∈ fiberDerivativeModule f ∧
    ∃ a : FiberBase →ᵃ[FiberField] FiberField,
      ∀ v : FiberBase, f v = h v + a v

/-- Claim 31835: the two exact regular copies are conjugate inside their
    actual generated image exactly for derivative-module plus affine
    differences. -/
def actualImageConjugacyCriterion_claim31835 : Prop :=
  ∀ (f : FiberFunction), f 0 = 0 →
    (actualImageConjugacy f ↔ affineDifferenceMembership f)

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim31835
