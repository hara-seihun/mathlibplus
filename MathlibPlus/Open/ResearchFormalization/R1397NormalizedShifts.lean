import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1397NormalizedShifts

abbrev F3 := ZMod 3
abbrev ShiftBase := F3 × F3
abbrev NormalizedShift := ShiftBase → F3

def normalized (s : NormalizedShift) : Prop :=
  s (0, 0) = 0

def shiftMonomials : Fin 8 → NormalizedShift :=
  ![
    (fun x => x.1),
    (fun x => x.2),
    (fun x => x.1 ^ 2),
    (fun x => x.1 * x.2),
    (fun x => x.2 ^ 2),
    (fun x => x.1 ^ 2 * x.2),
    (fun x => x.1 * x.2 ^ 2),
    (fun x => x.1 ^ 2 * x.2 ^ 2)
  ]

def shiftExpansion (coeff : Fin 8 → F3) : NormalizedShift :=
  fun x => ∑ i : Fin 8, coeff i * shiftMonomials i x

def normalizedShiftExpansion : Prop :=
  ∀ s : NormalizedShift, normalized s →
    ∃! coeff : Fin 8 → F3, ∀ x : ShiftBase,
      s x = shiftExpansion coeff x

def normalizedShiftCount : Prop :=
  Nat.card {s : NormalizedShift // normalized s} = 3 ^ 8

/-- Every normalized `F₃²`-profile has the eight displayed monomials as its
unique coefficient basis, and there are exactly `3⁸ = 6561` such profiles. -/
def allNormalizedShiftsCoefficientBasis : Prop :=
  normalizedShiftExpansion ∧
    normalizedShiftCount ∧
    (3 : ℕ) ^ 8 = 6561

end MathlibPlus.Open.ResearchFormalization.R1397NormalizedShifts
