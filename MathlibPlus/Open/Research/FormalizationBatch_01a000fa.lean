import Mathlib

namespace MathlibPlus.Open.Research

/-- Base-two entropy of a Bernoulli parameter. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  -(p * Real.log p + (1 - p) * Real.log (1 - p)) / Real.log 2

/-- Base-two entropy of a finitely supported table on a finite type. -/
noncomputable def finiteEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ a : α, p a * Real.log (p a) / Real.log 2

/-- The one-coordinate marginal of a law on finite subsets. -/
noncomputable def coordinateMarginal {X : Type*} [Fintype X] [DecidableEq X]
    (p : Finset X → ℝ) (x : X) : ℝ :=
  ∑ A : Finset X, if x ∈ A then p A else 0

/-- Total correlation of a law on finite subsets. -/
noncomputable def totalCorrelation {X : Type*} [Fintype X] [DecidableEq X]
    (p : Finset X → ℝ) : ℝ :=
  (∑ x : X, binaryEntropy (coordinateMarginal p x)) - finiteEntropy p

/-- The uniform law on a nonempty finite family, extended by zero off the family. -/
noncomputable def uniformLaw {X : Type*} [Fintype X] [DecidableEq X]
    (F : Finset (Finset X)) (A : Finset X) : ℝ :=
  if A ∈ F then 1 / (F.card : ℝ) else 0

/-- The union of a finite tuple of finite subsets. -/
def tupleUnion {X : Type*} [Fintype X] [DecidableEq X]
    {k : ℕ} (w : Fin k → Finset X) : Finset X :=
  (Finset.univ : Finset (Fin k)).biUnion w

/-- The law of the union of k independent uniform members of F. -/
noncomputable def unionLaw {X : Type*} [Fintype X] [DecidableEq X]
    (F : Finset (Finset X)) (k : ℕ) (U : Finset X) : ℝ :=
  ∑ w : Fin k → Finset X,
    if (∀ i, w i ∈ F) ∧ tupleUnion w = U then
      (1 / (F.card : ℝ)) ^ k
    else 0

/-- The scalar root relation defining the k-fold Bernoulli-union threshold. -/
def unionThresholdRoot (k : ℕ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ < (1 / 2 : ℝ) ∧ (1 - ρ) ^ k = ρ

/-- Claim 45912: the Bernoulli union entropy thresholds. -/
def claim45912 : Prop :=
  (∀ p : ℝ, 0 < p → p < (1 / 2 : ℝ) →
      let q := 2 * p - p ^ 2
      binaryEntropy q > binaryEntropy p ↔ p < (3 - Real.sqrt 5) / 2) ∧
    (∀ k : ℕ, 2 ≤ k → ∃! ρ : ℝ, unionThresholdRoot k ρ) ∧
    (∀ k l : ℕ, 2 ≤ k → k < l →
      ∀ ρ σ : ℝ, unionThresholdRoot k ρ → unionThresholdRoot l σ → σ < ρ)

/-- Union-closedness of a finite family of finite subsets. -/
def finiteUnionClosed {X : Type*} [Fintype X] [DecidableEq X]
    (F : Finset (Finset X)) : Prop :=
  ∀ ⦃A B : Finset X⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- Claim 45909: total correlation bounds for random unions. -/
def claim45909 : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (F : Finset (Finset X)), F.Nonempty → finiteUnionClosed F →
    ∀ k : ℕ, 2 ≤ k →
      (∑ x : X,
          (binaryEntropy (1 - (1 - coordinateMarginal (uniformLaw F) x) ^ k) -
            binaryEntropy (coordinateMarginal (uniformLaw F) x))) ≤
          totalCorrelation (unionLaw F k) - totalCorrelation (uniformLaw F) ∧
        totalCorrelation (unionLaw F k) - totalCorrelation (uniformLaw F) ≤
          ((k - 1 : ℕ) : ℝ) * totalCorrelation (uniformLaw F)

noncomputable def graphCommonNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) : Finset V := by
  classical exact Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)

noncomputable def graphNeighborCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : ℕ :=
  (graphCommonNeighbors G x x).card

noncomputable def stronglyRegularGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n k lam mu : ℕ) : Prop :=
  Fintype.card V = n ∧
    (∀ x : V, graphNeighborCount G x = k) ∧
    (∀ ⦃x y : V⦄, x ≠ y →
      ((G.Adj x y → (graphCommonNeighbors G x y).card = lam) ∧
       (¬ G.Adj x y → (graphCommonNeighbors G x y).card = mu)))

noncomputable def graphAdjacencyMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Matrix V V ℝ := by
  classical exact fun x y => if G.Adj x y then 1 else 0

noncomputable def graphAdjacencyOperator {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : (V → ℝ) →ₗ[ℝ] V → ℝ :=
  Matrix.toLin' (graphAdjacencyMatrix G)

noncomputable def graphEigenspace {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℝ) : Submodule ℝ (V → ℝ) :=
  LinearMap.ker (graphAdjacencyOperator G - r • LinearMap.id)

noncomputable def graphEigenMultiplicity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℝ) : ℕ :=
  Module.finrank ℝ (graphEigenspace G r)

/-- Claim 45929: the two restricted eigenvalues and their multiplicities. -/
def claim45929 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V),
    stronglyRegularGraph G 85 42 20 21 →
      graphEigenMultiplicity G ((-1 + Real.sqrt 85) / 2) = 42 ∧
      graphEigenMultiplicity G ((-1 - Real.sqrt 85) / 2) = 42

end MathlibPlus.Open.Research
