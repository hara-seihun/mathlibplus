import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Schur

open scoped BigOperators

noncomputable section

/-- Boundary coordinates of a kernel, with indices beginning at zero. -/
def boundaryCoordinate (K : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  K 0 (n - 1)

/-- Action-edge coordinates of a kernel. -/
def actionEdgeCoordinate (K : ℕ → ℕ → ℝ) (r s : ℕ) : ℝ :=
  K (r - 1) s - K r (s - 1)

/-- The boundary and action-edge coordinate definitions on their stated
index ranges. -/
def boundaryAndActionEdgeCoordinates : Prop :=
  ∀ (K : ℕ → ℕ → ℝ) (n r s : ℕ),
    1 ≤ n → 1 ≤ s → s < r →
      boundaryCoordinate K n = K 0 (n - 1) ∧
        actionEdgeCoordinate K r s = K (r - 1) s - K r (s - 1)

/-- First Schur mutation, after deleting the pivot row and column. -/
def schurMutation (K : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun r s => K (r + 1) (s + 1) -
    K (r + 1) 0 * K 0 (s + 1) / K 0 0

/-- The displayed first Schur-complement mutation under a nonzero pivot. -/
def schurMutationFormula : Prop :=
  ∀ (K : ℕ → ℕ → ℝ), K 0 0 ≠ 0 →
    ∀ r s,
      schurMutation K r s =
        K (r + 1) (s + 1) -
          K (r + 1) 0 * K 0 (s + 1) / K 0 0

/-- Recursive Schur--Green cone membership.  The size `n` records the
available finite kernel indices; the recursive clause mutates away the pivot. -/
def recursiveSchurGreenCone : ℕ → (ℕ → ℕ → ℝ) → Prop
  | 0, _ => True
  | n + 1, K =>
      K 0 0 > 0 ∧
      (∀ j, j < n + 1 → K 0 j > 0) ∧
      (∀ r s, r < n + 1 → s < n + 1 → 1 ≤ s → s < r →
        actionEdgeCoordinate K r s > 0) ∧
      recursiveSchurGreenCone n (schurMutation K)

/-- The exact mutated-boundary law. -/
def mutatedBoundaryLaw : Prop :=
  ∀ (K : ℕ → ℕ → ℝ) (n : ℕ),
    K 0 0 ≠ 0 →
      boundaryCoordinate (schurMutation K) (n + 1) =
        K 1 (n + 1) -
          boundaryCoordinate K 2 * boundaryCoordinate K (n + 2) /
            boundaryCoordinate K 1

/-- The exact mutated-edge law. -/
def mutatedEdgeLaw : Prop :=
  ∀ (K : ℕ → ℕ → ℝ) (r s : ℕ),
    K 0 0 ≠ 0 → 1 ≤ s → s < r →
      actionEdgeCoordinate (schurMutation K) r s =
        actionEdgeCoordinate K (r + 1) (s + 1) +
          (boundaryCoordinate K (r + 2) * boundaryCoordinate K (s + 1) -
            boundaryCoordinate K (r + 1) * boundaryCoordinate K (s + 2)) /
            boundaryCoordinate K 1

/-- Symmetry on the finite `n` by `n` part of a kernel. -/
def SymmetricOn (n : ℕ) (K : ℕ → ℕ → ℝ) : Prop :=
  ∀ i j, i < n → j < n → K i j = K j i

/-- Positive definiteness of the finite part of a kernel. -/
def PositiveDefiniteOn (n : ℕ) (K : ℕ → ℕ → ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    (∃ i, x i ≠ 0) →
      0 < ∑ i : Fin n, x i * (∑ j : Fin n, K (i : ℕ) (j : ℕ) * x j)

/-- An `LDLᵀ` factorization with unit lower factor and positive diagonal. -/
def HasPositiveLDL (n : ℕ) (K : ℕ → ℕ → ℝ) : Prop :=
  ∃ L D : ℕ → ℕ → ℝ,
    (∀ i, i < n → L i i = 1) ∧
    (∀ i j, i < n → j < n → i < j → L i j = 0) ∧
    (∀ i j, i < n → j < n → i ≠ j → D i j = 0) ∧
    (∀ i, i < n → D i i > 0) ∧
    (∀ i j, i < n → j < n →
      K i j = ∑ k ∈ Finset.range n, L i k * D k k * L j k)

/-- Recursive cone membership yields a positive-diagonal `LDLᵀ` factorization
and positive definiteness for every finite symmetric member. -/
def coneMembershipGivesPositiveLDL : Prop :=
  ∀ (n : ℕ) (K : ℕ → ℕ → ℝ),
    recursiveSchurGreenCone n K →
      SymmetricOn n K →
        HasPositiveLDL n K ∧ PositiveDefiniteOn n K

end

end MathlibPlus.Open.ResearchBatch.Schur
