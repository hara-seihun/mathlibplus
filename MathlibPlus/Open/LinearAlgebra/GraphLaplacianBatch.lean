import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.ResearchBatch

noncomputable section

/-- The explicit graph-Laplacian interface used by claims 49744--49745. -/
def graphLaplacianData {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, i ≠ j → Q i j = -w i j) ∧
    (∀ i j, w i j = w j i) ∧
    (∀ i, w i i = 0) ∧
    (∀ i j, 0 ≤ w i j) ∧
    (∀ i, Q i i = ∑ j : Fin n, if i = j then 0 else w i j) ∧
    (∀ i, ∑ j : Fin n, Q i j = 0)

/-- Claim 49744: the quadratic form of a complete policy's graph Laplacian
is the weighted sum over unordered edges.  The policy carrier is reduced only
to the displayed graph-Laplacian equations. -/
def claim49744_graphLaplacianEnergy : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → Fin n → ℝ) (k : Fin n → ℝ),
    graphLaplacianData Q w →
      dotProduct k (Q.mulVec k) =
        ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, w i j * (k i - k j) ^ 2

/-- The Boolean pair energy and its affine adjustment. -/
def binaryPairEnergy {n : ℕ} (w : Fin n → Fin n → ℝ)
    (a : Fin n → ℝ) (β : ℝ) (z : Fin n → ℝ) : ℝ :=
  4 * (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, w i j * |z i - z j|) -
    2 * ∑ i : Fin n, a i * z i + ∑ i : Fin n, a i - β

/-- Claim 49745: Boolean substitution gives the cut energy and retains the
constant term of the affine tangent exactly. -/
def claim49745_booleanAffineEnergy : Prop :=
  ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → Fin n → ℝ) (z k : Fin n → ℝ)
    (a : Fin n → ℝ) (β : ℝ),
    graphLaplacianData Q w →
      (∀ i, z i = 0 ∨ z i = 1) →
      (∀ i, k i = 2 * z i - 1) →
      dotProduct k (Q.mulVec k) =
          4 * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
            w i j * |z i - z j| ∧
        dotProduct k (Q.mulVec k) - (β + ∑ i : Fin n, a i * k i) =
          binaryPairEnergy w a β z

/-- Meet and join of Boolean output assignments. -/
def boolMeet {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool :=
  fun i => x i && y i

def boolJoin {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool :=
  fun i => x i || y i

def boolValue {n : ℕ} (z : Fin n → Bool) : Fin n → ℝ :=
  fun i => if z i then 1 else 0

def mergeLabels {n : ℕ} (terminal : Fin n → Bool)
    (x free : Fin n → Bool) : Fin n → Bool :=
  fun i => if terminal i then x i else free i

/-- The minimum over all assignments on the nonterminal coordinates. -/
def partiallyMinimizedEnergy {n : ℕ}
    (w : Fin n → Fin n → ℝ) (a : Fin n → ℝ) (β : ℝ)
    (terminal : Fin n → Bool) (x : Fin n → Bool) : ℝ :=
  sInf {v : ℝ | ∃ free : Fin n → Bool,
    v = binaryPairEnergy w a β (boolValue (mergeLabels terminal x free))}

def isFreeMinimizer {n : ℕ}
    (w : Fin n → Fin n → ℝ) (a : Fin n → ℝ) (β : ℝ)
    (terminal : Fin n → Bool) (x free : Fin n → Bool) : Prop :=
  ∀ free' : Fin n → Bool,
    binaryPairEnergy w a β (boolValue (mergeLabels terminal x free)) ≤
      binaryPairEnergy w a β (boolValue (mergeLabels terminal x free'))

/-- Claim 49747: nonnegative pair capacities make the full binary energy
submodular, and partial minimization over free output labels preserves that
submodularity on the terminal labels. -/
def claim49747_minCutSubmodularity : Prop :=
  ∀ (n : ℕ) (w : Fin n → Fin n → ℝ)
    (a : Fin n → ℝ) (β : ℝ) (terminal : Fin n → Bool),
    (∀ i j, 0 ≤ w i j) →
      (∀ x y : Fin n → Bool,
        binaryPairEnergy w a β (boolValue x) +
            binaryPairEnergy w a β (boolValue y) ≥
          binaryPairEnergy w a β (boolValue (boolMeet x y)) +
            binaryPairEnergy w a β (boolValue (boolJoin x y))) ∧
      (∀ x y u v : Fin n → Bool,
        isFreeMinimizer w a β terminal x u →
        isFreeMinimizer w a β terminal y v →
        binaryPairEnergy w a β (boolValue (mergeLabels terminal x u)) +
            binaryPairEnergy w a β (boolValue (mergeLabels terminal y v)) ≥
          partiallyMinimizedEnergy w a β terminal (boolMeet x y) +
            partiallyMinimizedEnergy w a β terminal (boolJoin x y)) ∧
      (∀ x y : Fin n → Bool,
        partiallyMinimizedEnergy w a β terminal x +
            partiallyMinimizedEnergy w a β terminal y ≥
          partiallyMinimizedEnergy w a β terminal (boolMeet x y) +
            partiallyMinimizedEnergy w a β terminal (boolJoin x y))

end

end MathlibPlus.Open.LinearAlgebra.ResearchBatch
