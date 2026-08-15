import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationR0577

/-- The integral bilinear form represented by a Gram matrix. -/
def integerBilinear {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ)
    (x y : Fin n → ℤ) : ℤ :=
  ∑ i, x i * ∑ j, G i j * y j

/-- The same form after extending scalars to the rationals. -/
def rationalBilinear {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ)
    (x y : Fin n → ℚ) : ℚ :=
  ∑ i, x i * ∑ j, (G i j : ℚ) * y j

/-- A nondegenerate symmetric integral Gram matrix. -/
def integralLatticeMatrix {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, G i j = G j i) ∧ Matrix.det G ≠ 0

/-- A primitive vector has no non-unit common integral divisor. -/
def primitiveVector {n : ℕ} (r : Fin n → ℤ) : Prop :=
  ∀ q : ℤ, (∀ i, q ∣ r i) → q = 1 ∨ q = -1

/-- The positive generator of the ideal of pairings with a vector. -/
def isDivisibility {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ)
    (r : Fin n → ℤ) (d : ℤ) : Prop :=
  0 < d ∧
    (∀ x : Fin n → ℤ, ∃ k : ℤ, integerBilinear G r x = d * k) ∧
    (∃ x : Fin n → ℤ, integerBilinear G r x = d)

/-- The columns of B are a Z-basis of the integral orthogonal complement of r. -/
def orthogonalComplementBasis {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) (r : Fin n → ℤ)
    (B : Matrix (Fin n) (Fin (n - 1)) ℤ) : Prop :=
  (∀ j, integerBilinear G r (fun i => B i j) = 0) ∧
    (∀ x : Fin n → ℤ,
      integerBilinear G r x = 0 ↔
        ∃ z : Fin (n - 1) → ℤ, B.mulVec z = x) ∧
    (∀ z z' : Fin (n - 1) → ℤ, B.mulVec z = B.mulVec z' → z = z')

/-- The restricted Gram matrix of the columns of B. -/
def restrictedGram {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) (B : Matrix (Fin n) (Fin (n - 1)) ℤ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ :=
  fun i j => integerBilinear G (fun k => B k i) (fun k => B k j)

/--
The root-complement determinant formula, in coordinates: every integral basis of
rᗮ has the asserted determinant.
-/
def claim26225 : Prop :=
  ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (r : Fin n → ℤ) (d : ℤ)
    (B : Matrix (Fin n) (Fin (n - 1)) ℤ),
    integralLatticeMatrix G →
    primitiveVector r →
    integerBilinear G r r = 2 →
    isDivisibility G r d →
    orthogonalComplementBasis G r B →
    d ^ 2 * Matrix.det (restrictedGram G B) = 2 * Matrix.det G

/-- The exact rank-seven Gram matrix in the exceptional determinant-five claim. -/
def exceptionalGram : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0,  0,  0,  1,  1,  1;
      0,  3, -1, -2, -1,  0,  1;
      0, -1,  3,  0,  0,  1,  1;
      0, -2,  0,  4,  2,  1, -1;
      1, -1,  0,  2,  2,  1,  0;
      1,  0,  1,  1,  1,  2,  1;
      1,  1,  1, -1,  0,  1,  2 ]

/-- A rational vector is integral when all its coordinates are integral. -/
def integerCoordinates {n : ℕ} (x : Fin n → ℚ) : Prop :=
  ∀ i, ∃ z : ℤ, x i = z

/-- Membership in the dual of the integral lattice with Gram matrix G. -/
def dualVector {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℚ) : Prop :=
  ∀ z : Fin n → ℤ,
    ∃ k : ℤ,
      rationalBilinear G (fun i => (z i : ℚ)) x = k

/-- Two rational coordinate vectors represent the same discriminant class. -/
def congruentModuloIntegral {n : ℕ} (x y : Fin n → ℚ) : Prop :=
  ∀ i, ∃ z : ℤ, x i - y i = z

/-- A displayed dual generator gives a cyclic discriminant group of order five. -/
def cyclicDiscriminantWithGenerator {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) : Prop :=
  dualVector G x ∧
    ¬ integerCoordinates x ∧
    (∀ i, ∃ z : ℤ, 5 * x i = z) ∧
    ∀ y : Fin n → ℚ, dualVector G y →
      ∃ k : Fin 5, congruentModuloIntegral y (fun i => (k.1 : ℚ) * x i)

/-- The displayed generator has discriminant pairing class 3/5. -/
def pairingClassThreeFifths {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) : Prop :=
  ∃ z : ℤ, rationalBilinear G x x = (3 : ℚ) / 5 + z

/-- Exact root count for a Gram matrix. -/
def hasExactlyRoots {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Prop :=
  let roots : Set (Fin n → ℤ) := {x | integerBilinear G x x = 2}
  roots.Finite ∧ roots.ncard = k

/-- A concrete generator of the discriminant group of the exceptional lattice. -/
def exceptionalDualGenerator : Fin 7 → ℚ :=
  ![1, 8 / 5, 6 / 5, 4 / 5, 0, -1, -1]

/--
The exact exceptional rank-seven lattice: it is positive definite of determinant
five and minimum two, has 72 roots, cyclic discriminant, and pairing class 3/5.
-/
def claim26223 : Prop :=
  let G := exceptionalGram
  integralLatticeMatrix G ∧
    Matrix.det G = 5 ∧
    (∀ x : Fin 7 → ℤ, (∃ i, x i ≠ 0) → 2 ≤ integerBilinear G x x) ∧
    (∃ x : Fin 7 → ℤ, integerBilinear G x x = 2) ∧
    hasExactlyRoots G 72 ∧
    cyclicDiscriminantWithGenerator G exceptionalDualGenerator ∧
    pairingClassThreeFifths G exceptionalDualGenerator

end MathlibPlus.Open.ResearchFormalizationR0577
