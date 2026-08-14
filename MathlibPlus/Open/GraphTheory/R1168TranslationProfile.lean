import Mathlib

namespace MathlibPlus.Open.GraphTheory.R1168

/-- The eight-point permutation displayed in the admitted translation profile. -/
def baseAction (i : Fin 8) : Fin 8 :=
  ![0, 1, 6, 7, 4, 5, 2, 3] i

abbrev Base := ZMod 5 × Fin 8
abbrev Source := ZMod 7 × Base

/-- The source-coordinate relabeling attached to a profile. -/
def profileRelabeling (t : Base → ZMod 7) : Source → Source :=
  fun p => (p.1 + t p.2, (p.2.1, baseAction p.2.2))

/-- Claim 31782 (identically admitted again as claim 41546): in the stated
source coordinates, a normalized profile has the displayed relabeling. -/
def standardTranslationProfileRelabeling_31782 : Prop :=
  ∀ (t : Base → ZMod 7),
    t (0, 0) = 0 →
      ∃! q : Source ≃ Source,
        ∀ (x : ZMod 7) (r : ZMod 5) (i : Fin 8),
          q (x, (r, i)) = (x + t (r, i), (r, baseAction i))

end MathlibPlus.Open.GraphTheory.R1168
