import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Invariance of a graph under simultaneous translation in the `F₅` coordinate. -/
def PInvariantGraph {X : Type*}
    (Γ : SimpleGraph (ZMod 5 × X)) : Prop :=
  ∀ a z w x y,
    Γ.Adj ((z, x) : ZMod 5 × X) ((w, y) : ZMod 5 × X) ↔
      Γ.Adj ((z + a, x) : ZMod 5 × X) ((w + a, y) : ZMod 5 × X)

def vSet {X : Type*} (Γ : SimpleGraph (ZMod 5 × X)) (x y : X) : Set (ZMod 5) :=
  {d | Γ.Adj ((0, x) : ZMod 5 × X) ((d, y) : ZMod 5 × X)}

/-- The admitted translation-invariant graph claim. -/
def claim41083 : Prop :=
  ∀ (X : Type*) (Γ : SimpleGraph (ZMod 5 × X)),
    PInvariantGraph Γ →
      (∀ x y z w,
        Γ.Adj ((z, x) : ZMod 5 × X) ((w, y) : ZMod 5 × X) ↔
          w - z ∈ vSet Γ x y) ∧
      (∀ x y, vSet Γ y x = -vSet Γ x y) ∧
      (∀ x, (0 : ZMod 5) ∉ vSet Γ x x)

end MathlibPlus.Open.ResearchFormalization
