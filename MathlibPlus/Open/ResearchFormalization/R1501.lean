import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1501

noncomputable section

abbrev MarkerVector := Fin 3 → ZMod 7

def markerVector (a b c : ZMod 7) : MarkerVector := ![a, b, c]

def rigidMarkerSet : Finset MarkerVector :=
  { markerVector 0 0 1, -markerVector 0 0 1,
    markerVector 0 1 0, -markerVector 0 1 0,
    markerVector 1 0 0, -markerVector 1 0 0,
    markerVector 1 0 1, -markerVector 1 0 1,
    markerVector 1 2 3, -markerVector 1 2 3 }

def setwiseStabilizesMarker (φ : MarkerVector ≃ₗ[ZMod 7] MarkerVector) : Prop :=
  ∀ v, v ∈ rigidMarkerSet ↔ φ v ∈ rigidMarkerSet

/-- The ten-point marker has only the scalar symmetries I and -I and spans the space. -/
def tenPointRigidMarker : Prop :=
  (∀ φ : MarkerVector ≃ₗ[ZMod 7] MarkerVector,
    setwiseStabilizesMarker φ ↔
      ((∀ v, φ v = v) ∨ (∀ v, φ v = -v))) ∧
    Submodule.span (ZMod 7) (rigidMarkerSet : Set MarkerVector) = ⊤

end

end MathlibPlus.Open.ResearchFormalization.R1501
