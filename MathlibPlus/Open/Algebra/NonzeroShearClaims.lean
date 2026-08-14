import Mathlib

namespace MathlibPlus.Open.Algebra

abbrev TernaryField := ZMod 3
abbrev CarryTable := (TernaryField × TernaryField) → TernaryField

/-- The four displayed coordinates in the single-cubic transporter family. -/
structure CubicPoint where
  x : TernaryField
  u : TernaryField
  v : TernaryField
  w : TernaryField

/-- A normalized carry has the prescribed zero value. -/
def NormalizedCarry := {q : CarryTable // q (0, 0) = 0}

/-- The repeated-factor cubic top in the first coordinate. -/
def repeatedFactorTop (p : CubicPoint) : TernaryField := p.v ^ 2 * p.w

/-- The coefficient-one lower shear in the third coordinate. -/
def coefficientOneShear (p : CubicPoint) : TernaryField := p.v + p.w

/-- The normalized single-cubic nonzero-shear transporter. -/
def singleCubicTransporter (q : CarryTable) (p : CubicPoint) : CubicPoint :=
  { x := p.x + p.v ^ 2 * p.w
    u := p.u + q (p.v, p.w)
    v := p.v + p.w
    w := p.w }

/-- The same transporter with an explicitly named lower-shear coefficient. -/
def coefficientShearTransporter (c : TernaryField) (q : CarryTable)
    (p : CubicPoint) : CubicPoint :=
  { x := p.x + p.v ^ 2 * p.w
    u := p.u + q (p.v, p.w)
    v := p.v + c * p.w
    w := p.w }

/-- The coordinate change used to compare the two nonzero lower shears. -/
def shearCoordinateChange (p : CubicPoint) : CubicPoint :=
  { x := 2 * p.x
    u := p.u
    v := p.v
    w := 2 * p.w }

/-- Its displayed inverse, which is the same scalar change over `𝔽₃`. -/
def shearCoordinateChangeInv (p : CubicPoint) : CubicPoint :=
  { x := 2 * p.x
    u := p.u
    v := p.v
    w := 2 * p.w }

/-- Claim 33469: every normalized carry has the displayed single repeated-factor
cubic top and the nonzero coefficient-one lower shear. -/
def claim33469_normalizedSingleCubicNonzeroShearTransporter : Prop :=
  ∀ q : NormalizedCarry, ∀ p : CubicPoint,
    singleCubicTransporter q.1 p =
        { x := p.x + repeatedFactorTop p
          u := p.u + q.1 (p.v, p.w)
          v := coefficientOneShear p
          w := p.w } ∧
      repeatedFactorTop p = p.v ^ 2 * p.w ∧
      coefficientOneShear p = 1 * p.v + 1 * p.w ∧
      (1 : TernaryField) ≠ 0

/-- Claim 33474: the lower-shear coefficient two is conjugate to coefficient
one by the displayed coordinate map, with the carry reparameterized by
`q(v,2w)`. -/
def claim33474_shearTwoCoordinateEquivalence : Prop :=
  ∀ q : NormalizedCarry,
    let q₂ : CarryTable := fun a => q.1 (a.1, 2 * a.2)
    q₂ (0, 0) = 0 ∧
      (∀ p : CubicPoint,
        shearCoordinateChange
            (coefficientShearTransporter 1 q.1
              (shearCoordinateChangeInv p)) =
          coefficientShearTransporter 2 q₂ p) ∧
      (∀ p : CubicPoint,
        shearCoordinateChangeInv (shearCoordinateChange p) = p)

end MathlibPlus.Open.Algebra
