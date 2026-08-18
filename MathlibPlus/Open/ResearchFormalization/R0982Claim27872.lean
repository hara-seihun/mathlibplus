import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0982.Claim27885

namespace MathlibPlus.Open.ResearchFormalization.R0982Claim27872

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0982
open MathlibPlus.Open.Research.OrbitalCriteria

abbrev F3 := ZMod 3
abbrev QuadraticPlane := Plane 3

/-- The normalized quadratic functions in the displayed five-term basis. -/
def normalizedQuadraticFunction (φ : QuadraticPlane → F3) : Prop :=
  φ 0 = 0 ∧
    ∃ c₁ c₂ c₃ c₄ c₅ : F3,
      ∀ u : QuadraticPlane,
        φ u = c₁ * u.1 + c₂ * u.2 + c₃ * u.1 ^ 2 +
          c₄ * u.1 * u.2 + c₅ * u.2 ^ 2

/-- The displayed-transporter suborbit test for a normalized function. -/
def displayedTransporterSuborbitTest
    (φ : QuadraticPlane → F3) : Prop :=
  ∃ q : Equiv.Perm (Omega 3),
    isQPhi 3 φ q ∧
      fixesStabilizerOrbits q
        (planeFiberGroup 3 q : Set (Equiv.Perm (Omega 3))) 0

/-- Existence of an exact alternate conjugator in the relevant two-closure. -/
def hasAlternateExactConjugator
    (φ : QuadraticPlane → F3) : Prop :=
  ∃ q : Equiv.Perm (Omega 3),
    isQPhi 3 φ q ∧
      ∃ qc : Equiv.Perm (Omega 3),
        qc ∈ twoClosureOf
          (planeFiberGroup 3 q : Set (Equiv.Perm (Omega 3))) ∧
          conjugateSet qc
              (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
                Set (Equiv.Perm (Omega 3))) =
            conjugateSet q
              (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
                Set (Equiv.Perm (Omega 3)))

/-- Claim 27872: exactly 216 of the 243 normalized quadratic functions fail
only the displayed transporter test, while every one has an alternate exact
conjugator in the relevant two-closure. -/
def claim27872 : Prop :=
  Nat.card {φ : QuadraticPlane → F3 // normalizedQuadraticFunction φ} = 243 ∧
    Nat.card {φ : QuadraticPlane → F3 //
      normalizedQuadraticFunction φ ∧
        ¬ displayedTransporterSuborbitTest φ} = 216 ∧
    ∀ φ : QuadraticPlane → F3,
      normalizedQuadraticFunction φ → hasAlternateExactConjugator φ

end

end MathlibPlus.Open.ResearchFormalization.R0982Claim27872
