import MathlibPlus.Open.ResearchFormalization.R2056.C35886

namespace MathlibPlus.Open.ResearchFormalization.R2056C35887

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2056C35886

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The number of the four displayed rhombic cells incident with a point. -/
def cellIncidenceCount (p : Point) : ℕ :=
  (Finset.univ.filter
    (fun ij : Fin 2 × Fin 2 => p ∈ cellSet ij.1 ij.2)).card

/-- A hexagonal defect would require six displayed rhombic cells at one
    point; the finite four-cell carrier has no such defect. -/
def hexagonalDefect : Prop :=
  ∃ p : Point, cellIncidenceCount p = 6

def defectFreeRhombicDisk : Prop :=
  (∀ i j : Fin 2, cellIsRhombus i j) ∧
    faceToFace ∧
      ¬ hexagonalDefect

/-- The actual nine-point carrier, rather than an arbitrary finite point set. -/
def ninePointSet : Finset Point :=
  Finset.univ.image (fun st : Fin 3 × Fin 3 => gridPoint st.1 st.2)

def ninePointCarrier : Prop := ninePointSet.card = 9

/-- Equality of unoriented direction representatives. -/
def projectivelySame (p q : Point) : Prop := p = q ∨ p = -q

/-- Reduction of all four displayed direction classes to an arbitrary pair. -/
def twoDirectionReduction : Prop :=
  ∃ a b : Fin 4,
    a ≠ b ∧
      ¬ projectivelySame (directionVector a) (directionVector b) ∧
        ∀ i : Fin 4,
          projectivelySame (directionVector i) (directionVector a) ∨
            projectivelySame (directionVector i) (directionVector b)

def notTwoDirectionReduction : Prop := ¬ twoDirectionReduction

/-- The connected-rhombic implication is false on this actual carrier. -/
def connectedRhombicForcingFails : Prop :=
  ¬ ((embeddedFaceToFaceDisk ∧
      defectFreeRhombicDisk ∧ connectedGrid ∧ nonconvexDisk) →
    ((∀ i j : Fin 4, i ≠ j → directionCrossing i j) ∨
      twoDirectionReduction))

/-- Claim 35887: this exact nine-point carrier is a connected, embedded,
    face-to-face, defect-free nonconvex rhombic disk with triangle-free unit
    graph and K₂,₂ crossing, and it defeats reduction to any pair of direction
    classes.  The finite carrier supplies only the stated local obstruction. -/
def claim35887_routeObstructionAndScope : Prop :=
  embeddedFaceToFaceDisk ∧
    defectFreeRhombicDisk ∧
      connectedGrid ∧
        nonconvexDisk ∧
          ninePointCarrier ∧
            unitGraphTriangleFree ∧
              directionK22 ∧
                notClique ∧
                  notTwoDirectionReduction ∧
                    connectedRhombicForcingFails

end

end MathlibPlus.Open.ResearchFormalization.R2056C35887
