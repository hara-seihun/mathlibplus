import MathlibPlus.Open.C0083AreaFourCoordinates

namespace MathlibPlus.Open.C0083AreaFourCoordinates

noncomputable section

/-- The exceptional area-at-most-four shapes whose leading coefficient has an
extra factor of two. -/
def exceptionalLeadingFactor1253 : AreaShape1252 → ℤ
  | .twoOne => 2
  | .threeOne => 2
  | .twoOneOne => 2
  | _ => 1

/-- A polynomial on the exact Claim 1252 carrier represents the gauged
coordinate after the half-shift. -/
def representsCoordinate1253 (d : ℕ) (shape : AreaShape1252)
    (p : Polynomial ℤ) : Prop :=
  ∀ b : ℝ,
    Polynomial.eval₂ (Int.castRingHom ℝ) b p =
      gaugedCupCoordinate1252 shape d (b + 1 / 2)

/-- The degree and leading coefficient property for one available coordinate. -/
def coordinateDegreeLeading1253 (d : ℕ) (shape : AreaShape1252) : Prop :=
  let degree : ℕ := d * (d + 1) / 2
  ∃ p : Polynomial ℤ,
    representsCoordinate1253 d shape p ∧
      p.natDegree = degree ∧
      p.coeff degree =
        exceptionalLeadingFactor1253 shape *
          (Nat.factorial d : ℤ) * (2 : ℤ) ^ degree

/-- Claim 1253: with `D=d(d+1)/2`, every available area-at-most-four
coordinate has degree `D`; the shapes `(2,1)`, `(3,1)`, and `(2,1,1)` have
leading coefficient `2 d! 2^D`, and all other shapes have `d! 2^D`. -/
def claim1253 : Prop :=
  ∀ (d : ℕ) (shape : AreaShape1252),
    availableShape1252 (d + 1) shape →
      coordinateDegreeLeading1253 d shape

end

end MathlibPlus.Open.C0083AreaFourCoordinates
