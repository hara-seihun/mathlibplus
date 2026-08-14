import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1117

abbrev C7 := ZMod 7
abbrev A4 := (Equiv.Perm.sign (α := Fin 4)).ker

def affineChartSupport (scaling : A4 → C7ˣ) (offset : A4 → C7) : Set A4 :=
  {h | h ≠ 1 ∧ ∃ r : C7, (scaling h : C7) * r + offset h ≠ r}

def normalizedCommonAffineChartLift
    (f : Equiv.Perm (C7 × A4)) : Prop :=
  ∃ (scaling : A4 → C7ˣ) (offset : A4 → C7) (q : Equiv.Perm A4),
    (∀ (r : C7) (h : A4),
      f (r, h) = ((scaling h : C7) * r + offset h, q h)) ∧
    scaling 1 = 1 ∧ offset 1 = 0 ∧ q 1 = 1 ∧
    affineChartSupport scaling offset =
      {h | h ≠ 1 ∧ (scaling h ≠ 1 ∨ offset h ≠ 0)}

end MathlibPlus.Open.ResearchFormalization.R1117
