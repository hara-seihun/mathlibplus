import Mathlib
import MathlibPlus.Open.C0079NeighboringMinor

open scoped BigOperators

namespace MathlibPlus.Open.C0083AreaFourCoordinates

noncomputable section

inductive AreaShape1252
  | empty
  | one
  | two
  | oneOne
  | three
  | twoOne
  | oneOneOne
  | four
  | threeOne
  | twoTwo
  | twoOneOne
  | oneOneOneOne

def shapeParts1252 : AreaShape1252 → List ℕ
  | .empty => []
  | .one => [1]
  | .two => [2]
  | .oneOne => [1, 1]
  | .three => [3]
  | .twoOne => [2, 1]
  | .oneOneOne => [1, 1, 1]
  | .four => [4]
  | .threeOne => [3, 1]
  | .twoTwo => [2, 2]
  | .twoOneOne => [2, 1, 1]
  | .oneOneOneOne => [1, 1, 1, 1]

def shapeMinimumDimension1252 : AreaShape1252 → ℕ
  | .empty => 1
  | .one => 1
  | .two => 2
  | .oneOne => 2
  | .three => 3
  | .twoOne => 2
  | .oneOneOne => 3
  | .four => 4
  | .threeOne => 3
  | .twoTwo => 3
  | .twoOneOne => 3
  | .oneOneOneOne => 4

def shapeIsAreaFour1252 : AreaShape1252 → Prop
  | .four => True
  | .threeOne => True
  | .twoTwo => True
  | .twoOneOne => True
  | .oneOneOneOne => True
  | _ => False

def availableShape1252 (r : ℕ) (shape : AreaShape1252) : Prop :=
  2 ≤ r ∧ shapeMinimumDimension1252 shape ≤ r - 1

/-- The padded-partition row map, written with the packet's one-based
partition parts and zero padding. -/
def partitionRow1252 (shape : AreaShape1252) (d : ℕ) (i : Fin d) : ℕ :=
  i.1 + (shapeParts1252 shape).getD (d - 1 - i.1) 0

/-- The exact flagged array entry used by the determinant carrier. -/
def flaggedEntry1252 (a : ℝ) (k j : ℕ) : ℝ :=
  (k + 1 : ℝ) *
    MathlibPlus.Open.C0079.completeHomogeneousInt
      (2 * (j : ℤ) - (k : ℤ) - 1)
      (k + 2)
      (MathlibPlus.Open.C0079.consecutiveVariables a k)

/-- The flagged minor indexed by one of the twelve area-at-most-four
partitions. -/
def flaggedMinor1252 (shape : AreaShape1252) (d : ℕ) (a : ℝ) : ℝ :=
  Matrix.det (fun (i : Fin d) (j : Fin d) =>
    flaggedEntry1252 a (partitionRow1252 shape d i) (j.1 + 1))

def gaugedCupCoordinate1252 : AreaShape1252 → ℕ → ℝ → ℝ
  | .empty, d, a => flaggedMinor1252 .empty d a
  | .one, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a
  | .two, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .two d a
  | .oneOne, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .oneOne d a
  | .three, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .two d a - flaggedMinor1252 .three d a
  | .twoOne, d, a =>
      2 * flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .two d a + flaggedMinor1252 .oneOne d a -
        flaggedMinor1252 .twoOne d a
  | .oneOneOne, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .oneOne d a - flaggedMinor1252 .oneOneOne d a
  | .four, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .two d a - flaggedMinor1252 .three d a +
        flaggedMinor1252 .four d a
  | .threeOne, d, a =>
      2 * flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .two d a + flaggedMinor1252 .oneOne d a -
        flaggedMinor1252 .three d a - flaggedMinor1252 .twoOne d a +
        flaggedMinor1252 .threeOne d a
  | .twoTwo, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .two d a + flaggedMinor1252 .oneOne d a -
        flaggedMinor1252 .twoOne d a + flaggedMinor1252 .twoTwo d a
  | .twoOneOne, d, a =>
      2 * flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .two d a + flaggedMinor1252 .oneOne d a -
        flaggedMinor1252 .twoOne d a - flaggedMinor1252 .oneOneOne d a +
        flaggedMinor1252 .twoOneOne d a
  | .oneOneOneOne, d, a =>
      flaggedMinor1252 .empty d a - flaggedMinor1252 .one d a +
        flaggedMinor1252 .oneOne d a - flaggedMinor1252 .oneOneOne d a +
        flaggedMinor1252 .oneOneOneOne d a

def coordinatePolynomial1252 (r : ℕ) (shape : AreaShape1252) : Prop :=
  ∃ p : Polynomial ℤ,
    (∀ b : ℝ,
      Polynomial.eval₂ (Int.castRingHom ℝ) b p =
        gaugedCupCoordinate1252 shape (r - 1) (b + 1 / 2)) ∧
    (∀ n : ℕ, 0 ≤ p.coeff n) ∧
    (shapeIsAreaFour1252 shape →
      ∀ n : ℕ, n ≤ p.natDegree → 0 < p.coeff n)

/-- Claim 1252: every available area-at-most-four gauged coordinate is in
`Z>=0[b]`, and every area-four coordinate has strictly positive
coefficients. -/
def claim1252 : Prop :=
  ∀ (r : ℕ), 2 ≤ r →
    ∀ shape : AreaShape1252,
      availableShape1252 r shape → coordinatePolynomial1252 r shape

/-- Claim 1254: pointwise positivity and the exact boundary-zero set for the
same determinant and gauged-coordinate carrier. -/
def claim1254 : Prop :=
  ∀ (r : ℕ), 2 ≤ r →
    (∀ shape : AreaShape1252,
      availableShape1252 r shape →
        ∀ a : ℝ, 1 / 2 < a →
          0 < gaugedCupCoordinate1252 shape (r - 1) a) ∧
    (∀ shape : AreaShape1252,
      availableShape1252 r shape →
        (gaugedCupCoordinate1252 shape (r - 1) (1 / 2) = 0 ↔
          shape = .one ∨ (r = 4 ∧ shape = .oneOneOne)))

end

end MathlibPlus.Open.C0083AreaFourCoordinates
