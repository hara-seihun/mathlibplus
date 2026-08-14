import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2
namespace CyclicProfiles

abbrev C2Cube := Fin 3 → ZMod 2
abbrev C3Square := Fin 2 → ZMod 3
abbrev C2CubeC3Square := C2Cube × C3Square

abbrev C2 := ZMod 2
abbrev C3 := ZMod 3

/-- Sections of a connection set over the ternary quotient. -/
abbrev SectionedSet (K H : Type*) := H → Set K

def negSet {G : Type*} [Neg G] (S : Set G) : Set G :=
  {x | -x ∈ S}

def inverseClosed {K H : Type*} [Neg K] [Neg H]
    (S : SectionedSet K H) : Prop :=
  ∀ h x, x ∈ S h → -x ∈ S (-h)

def identityFree {K H : Type*} [Zero K] [Zero H]
    (S : SectionedSet K H) : Prop := (0 : K) ∉ S 0

def imageSection {K H : Type*}
    (q : H → Equiv.Perm K) (S : SectionedSet K H) : SectionedSet K H :=
  fun h => q h '' S h

def activeSection {K H : Type*} [DecidableEq K]
    (q : H → Equiv.Perm K) (h : H) : Prop := q h ≠ 1

def identityBase {K H : Type*} [DecidableEq K] [Zero H]
    (q : H → Equiv.Perm K) : Prop := q 0 = 1

/-- Claim 29778: an active section is fixed once the source and target
inverse closures and the inactive inverse section are all imposed. -/
def claim_29778 : Prop :=
  ∀ (q : C3Square → Equiv.Perm C2Cube)
    (S T : SectionedSet C2Cube C3Square),
    inverseClosed S → inverseClosed T →
      (∀ h, T h = imageSection q S h) →
      (∀ h, activeSection q h → ¬ activeSection q (-h)) →
      (∀ h, S (-h) = negSet (S h)) →
      (∀ h, activeSection q h → T (-h) = negSet (S h)) →
      (∀ h, activeSection q h → imageSection q S h = S h)

/-- The image operation is the profile's actual action on sections. -/
def profileMoves {K H : Type*}
    (q : H → Equiv.Perm K) (S : SectionedSet K H) : Prop :=
  ∃ h, imageSection q S h ≠ S h

/-- Claim 29780: an identity-base breaker that still moves an ordinary
inverse-closed connection set must activate an inverse pair in `C₃²`. -/
def claim_29780 : Prop :=
  ∀ (q : C3Square → Equiv.Perm C2Cube)
    (S : SectionedSet C2Cube C3Square),
    identityBase q → identityFree S → inverseClosed S →
      inverseClosed (imageSection q S) → profileMoves q S →
      ∃ c : C3Square,
        c ≠ 0 ∧ activeSection q c ∧ activeSection q (-c)

def pairedSwapProfile (c : C3) : C3 → Equiv.Perm C2 :=
  fun h => if h = c ∨ h = -c then Equiv.swap 0 1 else 1

def pairedSource (c : C3) : SectionedSet C2 C3 :=
  fun h => if h = c ∨ h = -c then ({0} : Set C2) else ∅

def pairedTarget (c : C3) : SectionedSet C2 C3 :=
  imageSection (pairedSwapProfile c) (pairedSource c)

/-- Claim 29781: the paired support on `C₂ × C₃` is a concrete moved,
identity-free, inverse-closed counterfeit. -/
def claim_29781 : Prop :=
  ∀ c : C3, c ≠ 0 →
    let S := pairedSource c
    let T := pairedTarget c
    inverseClosed S ∧ inverseClosed T ∧ identityFree S ∧ identityFree T ∧
      S c = ({0} : Set C2) ∧ S (-c) = ({0} : Set C2) ∧
      T c = ({1} : Set C2) ∧ T (-c) = ({1} : Set C2) ∧
      S ≠ T ∧
      activeSection (pairedSwapProfile c) c ∧
      activeSection (pairedSwapProfile c) (-c)

end CyclicProfiles
end MathlibPlus.Open.NewResearch2
