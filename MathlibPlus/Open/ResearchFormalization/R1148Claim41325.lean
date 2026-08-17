import MathlibPlus.Open.ResearchFormalization.R1148Claim41323
import MathlibPlus.Open.ResearchFormalization.R1148Claim41327

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim41325

abbrev F7 := MathlibPlus.Open.ResearchFormalization.R1148Claim41323.F7
abbrev V := MathlibPlus.Open.ResearchFormalization.R1148Claim41323.V

open MathlibPlus.Open.ResearchFormalization.R1148Claim41323
open MathlibPlus.Open.ResearchFormalization.R1148Claim41327

def properFiber (B : Set V) (x : F7) : Prop :=
  (verticalFiber B x).Nonempty ∧
    verticalFiber B x ≠ (Set.univ : Set F7)

def atLeastTwoProperFibers (B : Set V) : Prop :=
  ∃ x y : F7, x ≠ y ∧ properFiber B x ∧ properFiber B y

def singletonFiber (S : Set F7) : Prop :=
  ∃ a : F7, S = ({a} : Set F7)

def coSingletonFiber (S : Set F7) : Prop :=
  ∃ a : F7, S = ({a} : Set F7)ᶜ

def cyclicFanoLine (S : Set F7) : Prop :=
  S ∈ fanoA ∨ S ∈ fanoB

def cyclicFanoLineComplement (S : Set F7) : Prop :=
  S ∈ lineComplementFamily fanoA ∨
    S ∈ lineComplementFamily fanoB

def exceptionalFiber (S : Set F7) : Prop :=
  singletonFiber S ∨
    coSingletonFiber S ∨
    cyclicFanoLine S ∨
    cyclicFanoLineComplement S

def nonExceptionalProperFiber (B : Set V) : Prop :=
  ∃ x : F7,
    properFiber B x ∧ ¬ exceptionalFiber (verticalFiber B x)

def differentCyclicFanoLineFibers (B : Set V) : Prop :=
  ∃ x y : F7, x ≠ y ∧
    ((verticalFiber B x ∈ fanoA ∧ verticalFiber B y ∈ fanoB) ∨
      (verticalFiber B x ∈ fanoB ∧ verticalFiber B y ∈ fanoA))

def affineFiberForm (ε : F7) (σ : Equiv.Perm V) : Prop :=
  ∃ k d : F7,
    d ≠ 0 ∧
      ∀ x y : F7,
        σ (x, y) = (ε * x, k * x + d * y)

/-- Claim 41325: outside the singleton, co-singleton, and the two cyclic-Fano
line families (and their complements), the exact same-sign fiber branch is
forced into the triangular affine stabilizer. -/
def claim41325 : Prop :=
  ∀ (B : Set V) (ε : F7)
    (p q : F7 → F7 → F7) (σ τ : Equiv.Perm V),
    sameSignProfile ε p q σ τ →
    adjacentSetEquation B σ τ →
    atLeastTwoProperFibers B →
    (nonExceptionalProperFiber B ∨
      differentCyclicFanoLineFibers B) →
    affineFiberForm ε σ ∧
      σ ∈ triangularLinearStabilizer

end MathlibPlus.Open.ResearchFormalization.R1148Claim41325
