import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RepeatedPairShift

/-- The offset in the explicit repeated-pair detecting shift. -/
def repeatedPairOffset (Mstar N : ℕ) : ℕ :=
  max 0 ((Mstar - N + 1) / 2)

/-- The shift in the explicit repeated-pair detecting construction. -/
def repeatedPairDetectingShift (q Mstar N : ℕ)
    (_hparity : Mstar % 2 ≠ N % 2) : ℕ :=
  q + repeatedPairOffset Mstar N + 1

end MathlibPlus.Open.ResearchFormalization.RepeatedPairShift
