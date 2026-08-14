import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.CyclicSevenSquared

abbrev V7 := Fin 2 → ZMod 7
abbrev GL2_7 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)

def inverseClosedAdd (X : Finset V7) : Prop :=
  ∀ x : V7, x ∈ X ↔ -x ∈ X

def zeroFree (X : Finset V7) : Prop :=
  (0 : V7) ∉ X

def cayleyGraph (X : Finset V7) : SimpleGraph V7 :=
  SimpleGraph.fromRel (fun x y => y - x ∈ X)

def glAction (M : GL2_7) (x : V7) : V7 :=
  (M : Matrix (Fin 2) (Fin 2) (ZMod 7)).mulVec x

def glImage (M : GL2_7) (X : Finset V7) : Finset V7 := by
  classical
  exact X.image (glAction M)

/-- Ordinary undirected CI for the two-dimensional vector group over `𝔽₇`. -/
def ordinary_undirected_ci_c7_squared : Prop :=
  ∀ X Y : Finset V7,
    zeroFree X → inverseClosedAdd X →
    zeroFree Y → inverseClosedAdd Y →
    (Nonempty (cayleyGraph X ≃g cayleyGraph Y) ↔
      ∃ M : GL2_7, glImage M X = Y)

end MathlibPlus.Open.ResearchFormalization.CyclicSevenSquared
