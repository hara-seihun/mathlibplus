import Mathlib

attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.ResearchFormalizationBatch01

abbrev C3Plane := Fin 2 → ZMod 3

noncomputable def displacementSubgroup (q : Equiv.Perm C3Plane) : AddSubgroup C3Plane :=
  AddSubgroup.closure {x | ∃ t : C3Plane, x = t - q t + q 0}

def congruentModulo (L : AddSubgroup C3Plane) (x y : C3Plane) : Prop :=
  x - y ∈ L

def inducesTranslationModulo (q : Equiv.Perm C3Plane) (L : AddSubgroup C3Plane) : Prop :=
  ∀ t : C3Plane, congruentModulo L (q t) (t + q 0)

def ternaryLine (L : AddSubgroup C3Plane) : Prop :=
  Fintype.card L = 3

def isTranslationOnC3Plane (q : Equiv.Perm C3Plane) : Prop :=
  ∃ c : C3Plane, ∀ t, q t = t + c

def displacementSpanCriterionForC3Plane : Prop :=
  ∀ (q : Equiv.Perm C3Plane) (L : AddSubgroup C3Plane),
    ternaryLine L →
      (displacementSubgroup q ≤ L ↔ inducesTranslationModulo q L) ∧
      (Fintype.card {r : Equiv.Perm C3Plane //
          inducesTranslationModulo r L} = 648) ∧
      (Fintype.card {r : Equiv.Perm C3Plane //
          inducesTranslationModulo r L ∧ isTranslationOnC3Plane r} = 9) ∧
      (Fintype.card {r : Equiv.Perm C3Plane //
          inducesTranslationModulo r L ∧ displacementSubgroup r = L} = 639)

end MathlibPlus.Open.ResearchFormalizationBatch01
