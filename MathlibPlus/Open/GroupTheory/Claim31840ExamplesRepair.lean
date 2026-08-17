import MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837
import MathlibPlus.Open.ResearchFormalization.R1171Claim41590

namespace MathlibPlus.Open.GroupTheory.Claim31840Examples

noncomputable section

abbrev F := MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837.FiberField
abbrev V := MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837.FiberBase
abbrev Ω := MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837.FiberOmega
abbrev FunctionSpace :=
  MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837.FiberFunction

open MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837

/-- Affineness of the function component of the actual generated image
`Y_f=M_f⋊V`, rather than membership of the original shear profile in an
auxiliary sum. -/
def actualGeneratedImageAffine (f : FunctionSpace) : Prop :=
  ∀ h : FunctionSpace, h ∈ fiberDerivativeModule f →
    ∃ a : V →ᵃ[F] F, ∀ v : V, h v = a v

/-- The actual intersection of the source and target subgroup copies. -/
def fiberIntersection (f : FunctionSpace) : Subgroup (Equiv.Perm Ω) :=
  fiberTranslations ⊓ fiberTarget f

/-- Conjugacy by an element of the actual two-closure of the generated image. -/
def conjugacyInActualTwoClosure (f : FunctionSpace)
    (R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ a : Equiv.Perm Ω,
    a ∈ fiberTwoClosure f ∧
      MathlibPlus.Open.ResearchFormalization.R1171Claim41590.conjugateSubgroup
          a R = T

/-- The zero repair is tied to the actual derivative level set, the unchanged
regular target copy, and an actual two-closure conjugator. -/
def zeroRepairConjugacy (f : FunctionSpace) : Prop :=
  ∃ (Z : Submodule F V) (ell : V →ₗ[F] F),
    (Z : Set V) = fiberZ f ∧
      (∀ x : V, x ∈ fiberZ f →
        ∀ v : V, f (x + v) - f x = f v) ∧
        (∀ x : V, x ∈ Z → ell x = -f x) ∧
          fiberTarget (fun v : V => f v + ell v) = fiberTarget f ∧
            let q : Equiv.Perm Ω := fiberShear (fun v : V => f v + ell v)
            q ∈ fiberTwoClosure f ∧
              q⁻¹ ∈ fiberTwoClosure f ∧
                MathlibPlus.Open.ResearchFormalization.R1171Claim41590.conjugateSubgroup
                    q⁻¹ fiberTranslations = fiberTarget f

/-- Claim 31840: the literal one-coordinate quadratic and cubic fibre
shears have the stated derivative-module ranks, actual generated-image and
intersection orders, actual-image conjugacy behavior, zero repair, and
nonaffine cubic image. -/
def claim31840 : Prop :=
  let f₂ : FunctionSpace := fun v : V => (v 0) ^ 2
  let f₃ : FunctionSpace := fun v : V => (v 0) ^ 3
  f₂ 0 = 0 ∧
    f₃ 0 = 0 ∧
      Module.finrank F (fiberDerivativeModule f₂) = 2 ∧
        Nat.card (fiberGeneratedImage f₂) = (5 : ℕ) ^ 6 ∧
          Nat.card (fiberIntersection f₂) = (5 : ℕ) ^ 4 ∧
            ¬MathlibPlus.Open.ResearchFormalization.R1171Claim41590.conjugateInAmbient
                (fiberGeneratedImage f₂) fiberTranslations (fiberTarget f₂) ∧
              zeroRepairConjugacy f₂ ∧
                Module.finrank F (fiberDerivativeModule f₃) = 3 ∧
                  Nat.card (fiberGeneratedImage f₃) = (5 : ℕ) ^ 7 ∧
                    ¬actualGeneratedImageAffine f₃

end

end MathlibPlus.Open.GroupTheory.Claim31840Examples
