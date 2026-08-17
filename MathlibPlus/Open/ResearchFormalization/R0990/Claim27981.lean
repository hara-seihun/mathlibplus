import Mathlib
import MathlibPlus.Open.ResearchFormalization.CyclicSevenSquared

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0990

open MathlibPlus.Open.ResearchFormalization.CyclicSevenSquared

abbrev ConnectionSet :=
  {X : Finset V7 // zeroFree X ∧ inverseClosedAdd X}

def sameGLOrbit (X Y : ConnectionSet) : Prop :=
  ∃ M : GL2_7, glImage M X.1 = Y.1

def sameOrdinaryGraphType (X Y : ConnectionSet) : Prop :=
  Nonempty (cayleyGraph X.1 ≃g cayleyGraph Y.1)

def glOrbitRepresentatives (R : Finset ConnectionSet) : Prop :=
  R.card = 17794 ∧
    (∀ X : ConnectionSet, ∃! Y : ConnectionSet,
      Y ∈ R ∧ sameGLOrbit X Y) ∧
      (∀ X ∈ R, ∀ Y ∈ R, sameGLOrbit X Y → X = Y)

def graphTypeRepresentatives (R : Finset ConnectionSet) : Prop :=
  R.card = 17794 ∧
    (∀ X : ConnectionSet, ∃! Y : ConnectionSet,
      Y ∈ R ∧ sameOrdinaryGraphType X Y) ∧
      (∀ X ∈ R, ∀ Y ∈ R, sameOrdinaryGraphType X Y → X = Y)

/-- Claim 27981: the exact inverse-closed zero-free C₇² connection-set carrier
 has 17,794 GL(2,7) orbits and 17,794 ordinary graph types, of which
 17,790 are connected. -/
def exactGL2SevenSquaredOrbitAndGraphTypeCount_claim27981 : Prop := by
  classical
  exact ∃ glReps graphReps : Finset ConnectionSet,
    glOrbitRepresentatives glReps ∧
      graphTypeRepresentatives graphReps ∧
        (graphReps.filter (fun X : ConnectionSet =>
          SimpleGraph.Connected (cayleyGraph X.1))).card = 17790

end MathlibPlus.Open.ResearchFormalization.R0990
