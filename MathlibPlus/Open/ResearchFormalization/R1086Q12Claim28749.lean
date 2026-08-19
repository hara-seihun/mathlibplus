import Mathlib
import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.ResearchFormalization.R1086Q12Claim28749

noncomputable section

abbrev ThreeColor := Fin 3

/-- A three-color assignment with the identity fixed outside the atlas domain. -/
def threeColorAssignment {G : Type*} [Group G]
    (c : G → ThreeColor) : Prop :=
  c 1 = 0

def automorphismColorRelated {G : Type*} [Group G]
    (c d : G → ThreeColor) : Prop :=
  ∃ φ : G ≃* G, ∀ h : G, h ≠ 1 → c h = d (φ h)

def automorphismColorOrbit {G : Type*} [Group G]
    (c : G → ThreeColor) : Set (G → ThreeColor) :=
  {d | threeColorAssignment d ∧ automorphismColorRelated c d}

def automorphismColorOrbitFamily {G : Type*} [Group G]
    : Set (Set (G → ThreeColor)) :=
  {S | ∃ c : G → ThreeColor,
    threeColorAssignment c ∧ S = automorphismColorOrbit c}

def threeColorDirectedIso {G : Type*} [Group G]
    (c d : G → ThreeColor) (e : Equiv G G) : Prop :=
  e 1 = 1 ∧
    ∀ x y : G, x ≠ y →
      c (x⁻¹ * y) = d ((e x)⁻¹ * e y)

def fixedColorIsoClass {G : Type*} [Group G]
    (c : G → ThreeColor) : Set (G → ThreeColor) :=
  {d | threeColorAssignment d ∧
    ∃ e : Equiv G G, threeColorDirectedIso c d e}

def fixedColorIsoFamily {G : Type*} [Group G]
    : Set (Set (G → ThreeColor)) :=
  {S | ∃ c : G → ThreeColor,
    threeColorAssignment c ∧ S = fixedColorIsoClass c}

def threeColorDefectFree {G : Type*} [Group G]
    : Prop :=
  ∀ c d : G → ThreeColor,
    threeColorAssignment c →
    threeColorAssignment d →
    (∃ e : Equiv G G, threeColorDirectedIso c d e) →
    automorphismColorRelated c d

/-- Claim 28749: the exact three-color Q₁₂ atlas has 177147 assignments,
16524 automorphism orbits, the same number of fixed-color directed
isomorphism types, and no defect fiber. -/
def claim28749 : Prop :=
  ∀ {G : Type*} [Group G] [Fintype G]
    (a b : G),
    MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
      Set.ncard {c : G → ThreeColor | threeColorAssignment c} = 3 ^ 11 ∧
        Set.ncard {c : G → ThreeColor | threeColorAssignment c} = 177147 ∧
        Set.ncard (automorphismColorOrbitFamily (G := G)) = 16524 ∧
        Set.ncard (fixedColorIsoFamily (G := G)) = 16524 ∧
        threeColorDefectFree (G := G)

end

end MathlibPlus.Open.ResearchFormalization.R1086Q12Claim28749
