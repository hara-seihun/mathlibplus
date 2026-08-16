import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev RealCubeFunction (n : ℕ) := Cube n → ℝ

inductive DecisionTree (n : ℕ) where
  | leaf (value : Bool)
  | node (coordinate : Fin n) (ifFalse : DecisionTree n) (ifTrue : DecisionTree n)
  deriving DecidableEq

namespace DecisionTree

def eval : DecisionTree n → Cube n → Bool
  | .leaf value, _ => value
  | .node coordinate ifFalse ifTrue, x =>
      if x coordinate then eval ifTrue x else eval ifFalse x

def depth : DecisionTree n → ℕ
  | .leaf _ => 0
  | .node _ ifFalse ifTrue => max (depth ifFalse) (depth ifTrue) + 1

end DecisionTree

def boolAsReal (b : Bool) : ℝ := if b then 1 else 0

def treeFunction (tree : DecisionTree n) : RealCubeFunction n :=
  fun x => boolAsReal (tree.eval x)

def decisionTreeFunctions (n k : ℕ) : Set (RealCubeFunction n) :=
  {f | ∃ tree : DecisionTree n, tree.depth ≤ k ∧ f = treeFunction tree}

def treeConvexHull (n k : ℕ) : Set (RealCubeFunction n) :=
  convexHull ℝ (decisionTreeFunctions n k)

def cubeMonomial (coordinates : Finset (Fin n)) : RealCubeFunction n :=
  fun x => Finset.prod coordinates (fun coordinate => boolAsReal (x coordinate))

def multilinearPolynomialSpace (n r : ℕ) : Submodule ℝ (RealCubeFunction n) :=
  Submodule.span ℝ {monomial | ∃ coordinates : Finset (Fin n), coordinates.card ≤ r ∧
    monomial = cubeMonomial coordinates}

def degreeBound (n k : ℕ) : ℕ := min n k

def coefficientDimension (n k : ℕ) : ℕ :=
  Finset.sum (Finset.range (degreeBound n k + 1)) (fun j => Nat.choose n j)

def affineHullDimensionAndSupport (n k : ℕ) : Prop :=
  ((affineSpan ℝ (treeConvexHull n k) : AffineSubspace ℝ (RealCubeFunction n)) :
      Set (RealCubeFunction n)) =
      (multilinearPolynomialSpace n (degreeBound n k) : Set (RealCubeFunction n)) ∧
    Module.finrank ℝ (multilinearPolynomialSpace n (degreeBound n k)) =
      coefficientDimension n k

abbrev BilinearForm (n : ℕ) :=
  RealCubeFunction n →ₗ[ℝ] RealCubeFunction n →ₗ[ℝ] ℝ

def symmetricBilinear (form : BilinearForm n) : Prop :=
  ∀ g h, form g h = form h g

def positiveSemidefiniteBilinear (form : BilinearForm n) : Prop :=
  ∀ g, 0 ≤ form g g

def quadraticValue (form : BilinearForm n) (g : RealCubeFunction n) : ℝ :=
  form g g

def isConvexCombination (m n : ℕ) (weights : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ weights i) ∧ ∑ i, weights i = 1

def convexCombination (m n : ℕ) (weights : Fin m → ℝ)
    (functions : Fin m → RealCubeFunction n) : RealCubeFunction n :=
  ∑ i, weights i • functions i

def barycentricQuadraticValue (m n : ℕ) (form : BilinearForm n)
    (weights : Fin m → ℝ) (functions : Fin m → RealCubeFunction n) : ℝ :=
  ∑ i, ∑ j, weights i * weights j * form (functions i) (functions j)

def hullBound (n k : ℕ) {P : Type} [Fintype P]
    (forms : P → BilinearForm n) (K : ℝ) : Prop :=
  ∀ g, g ∈ treeConvexHull n k → ∃ π, quadraticValue (forms π) g ≤ K

def boundedSmallCombinations (n k : ℕ) {P : Type} [Fintype P]
    (forms : P → BilinearForm n) (K : ℝ) : Prop :=
  ∀ m, 1 ≤ m → m ≤ coefficientDimension n k →
    ∀ functions : Fin m → RealCubeFunction n,
      (∀ i, functions i ∈ decisionTreeFunctions n k) →
      ∀ weights : Fin m → ℝ,
        isConvexCombination m n weights →
        ∃ π, barycentricQuadraticValue m n (forms π) weights functions ≤ K

def fourierDimensionSparseRadialTestTheorem : Prop :=
  ∀ n k, affineHullDimensionAndSupport n k ∧
    ∀ (P : Type) [Fintype P] [Nonempty P]
      (forms : P → BilinearForm n),
      (∀ π, symmetricBilinear (forms π) ∧
        positiveSemidefiniteBilinear (forms π)) →
      ∀ K : ℝ, 0 ≤ K →
        (hullBound n k forms K ↔ boundedSmallCombinations n k forms K)

end MathlibPlus.Open.Analysis
