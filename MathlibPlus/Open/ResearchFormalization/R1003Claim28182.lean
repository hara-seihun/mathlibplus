import Mathlib
import MathlibPlus.Open.GraphTheory.EC35EightLowValencyCI

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28182

abbrev HCoordinate : Type := ZMod 5 × ZMod 8
abbrev GCoordinate : Type := ZMod 7 × HCoordinate

def hMul (a b : HCoordinate) : HCoordinate :=
  (a.1 + (-1 : ZMod 5) ^ a.2.val * b.1, a.2 + b.2)

def gMul (a b : GCoordinate) : GCoordinate :=
  (a.1 + (-1 : ZMod 7) ^ a.2.2.val * b.1, hMul a.2 b.2)

def coordinateAlpha (a : GCoordinate) : GCoordinate :=
  (a.1, (a.2.1, 3 * a.2.2))

def coordinateGroupAutomorphism : Prop :=
  Function.Bijective coordinateAlpha ∧
    ∀ a b, coordinateAlpha (gMul a b) =
      gMul (coordinateAlpha a) (coordinateAlpha b)

def c5Relators : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of (0 : Fin 2)) ^ 5,
    (FreeGroup.of (1 : Fin 2)) ^ 8,
    FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
      (FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of (0 : Fin 2)}

abbrev EC5 : Type := PresentedGroup c5Relators

/-- The coordinate law has the named `E(C₅,8)` identification, and the full
coordinate law has the named `𝔽₇ ⋊χ E(C₅,8) ≅ E(C₃₅,8)` identification. -/
def semidirectGroupIdentifications : Prop :=
  (∃ e : HCoordinate ≃ EC5,
    ∀ a b, e (hMul a b) = e a * e b) ∧
    ∃ e : GCoordinate ≃ MathlibPlus.Open.GraphTheory.EC35Eight,
      ∀ a b, e (gMul a b) = e a * e b

/-- Claim 28182: the displayed cubing map is the group automorphism of the
named `E(C₃₅,8)` group. -/
def universalCubingAutomorphism : Prop :=
  semidirectGroupIdentifications ∧
    coordinateGroupAutomorphism ∧
      ∃ e : GCoordinate ≃ MathlibPlus.Open.GraphTheory.EC35Eight,
        (∀ a b, e (gMul a b) = e a * e b) ∧
          ∃ α : MathlibPlus.Open.GraphTheory.EC35Eight ≃*
              MathlibPlus.Open.GraphTheory.EC35Eight,
            ∀ a, α (e a) = e (coordinateAlpha a)

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28182
