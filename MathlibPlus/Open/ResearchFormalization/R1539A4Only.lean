import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1539A4Only

noncomputable section

abbrev C5 := Multiplicative (ZMod 5)
abbrev A4 := alternatingGroup (Fin 4)
abbrev Omega := C5 × A4

def baseAction (t : C5) (g h : A4) (p : Omega) : Omega :=
  (t * p.1, g * p.2 * h)

def a4OnlyInversion (p : Omega) : Omega :=
  (p.1, p.2⁻¹)

def unorderedPair (P : Set Omega) : Prop :=
  P.ncard = 2

def baseOrbital (P : Set Omega) : Set (Set Omega) :=
  {Q | unorderedPair Q ∧
    ∃ t : C5, ∃ g h : A4,
      Set.image (baseAction t g h) P = Q}

def movedByA4OnlyInversion : Set (Set Omega) :=
  {P | unorderedPair P ∧
    baseOrbital P ≠ baseOrbital (Set.image a4OnlyInversion P)}

/-- Claim 37755: A4-only inversion moves exactly 960 of the 1770
unordered pairs between the actual generated X-orbitals. -/
def claim37755_a4OnlyInversionMoves960 : Prop :=
  Set.ncard {P : Set Omega | unorderedPair P} = 1770 ∧
    Set.ncard movedByA4OnlyInversion = 960

end

end MathlibPlus.Open.ResearchFormalization.R1539A4Only
