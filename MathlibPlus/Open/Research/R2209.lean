import Mathlib

namespace MathlibPlus.Open.Research.R2209

abbrev F3 := ZMod 3
abbrev Point := F3 × F3
abbrev IndexedPair := Point × Point

def digit (n k : Nat) : F3 :=
  ((n / 3 ^ k) % 3 : Nat)

def pointPairAt (n : Fin 81) : IndexedPair :=
  ((digit n 0, digit n 1), (digit n 2, digit n 3))

def addPoint (x y : Point) : Point :=
  (x.1 + y.1, x.2 + y.2)

def lowerBasis (k : Fin 5) : Point → F3
  | y =>
    match k with
    | 0 => y.1 ^ 2
    | 1 => y.1 * y.2
    | 2 => y.2 ^ 2
    | 3 => y.1 ^ 2 * y.2
    | 4 => y.1 * y.2 ^ 2

def delta (r : Point) (y : Point) (f : Point → F3) : F3 :=
  f (addPoint y r) - f y - f r

def lowerJetMatrix : Matrix (Fin 81) (Fin 5) F3 := fun row column =>
  let pair := pointPairAt row
  delta pair.1 pair.2 (lowerBasis column)

def lowerPolynomial (coefficients : Fin 5 → F3) : Point → F3 := fun y =>
  ∑ k : Fin 5, coefficients k * lowerBasis k y

def LowerJetInjective : Prop :=
  ∀ coefficients : Fin 5 → F3,
    (∀ r y : Point, delta r y (lowerPolynomial coefficients) = 0) →
      ∀ k, coefficients k = 0

def LowerJetRankFive : Prop :=
  Matrix.rank lowerJetMatrix = 5 ∧ LowerJetInjective

end MathlibPlus.Open.Research.R2209
