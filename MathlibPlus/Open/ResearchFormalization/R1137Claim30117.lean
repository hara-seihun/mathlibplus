import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1137Claim30117

abbrev A4Coordinates := Fin 12
abbrev PrimeProduct (p : ℕ) := ZMod p × A4Coordinates

/-- The retained one-based `12T90` coordinate map, written with zero-based labels. -/
def q12T90 : A4Coordinates → A4Coordinates :=
  ![0, 1, 9, 3, 4, 10, 6, 7, 11, 2, 5, 8]

def affineLift {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p) :
    PrimeProduct p → PrimeProduct p :=
  fun z =>
    ((lambda z.2 : ZMod p) * z.1 + tau z.2, q12T90 z.2)

/-- Claim 30117: the normalized common fibrewise affine lift over the retained
`12T90` coordinates has the displayed scalar and translation profiles. -/
def normalizedCommonFibrewiseAffineLift :
    ∀ (p : ℕ), (PrimeProduct p → PrimeProduct p) → Prop :=
  fun p f =>
    Nat.Prime p ∧ 5 ≤ p ∧
      ∃ (lambda : A4Coordinates → (ZMod p)ˣ)
        (tau : A4Coordinates → ZMod p),
        lambda 0 = 1 ∧ tau 0 = 0 ∧
          ∀ (x : ZMod p) (h : A4Coordinates),
            f (x, h) =
              ((lambda h : ZMod p) * x + tau h, q12T90 h)

end MathlibPlus.Open.ResearchFormalization.R1137Claim30117
