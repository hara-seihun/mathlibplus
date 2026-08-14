import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch.GraphAndEnergy

/-- A simple edge is a symmetric, non-diagonal pair represented by a two-element set. -/
def isSimpleEdge {V : Type*} [DecidableEq V] (e : Finset V) : Prop :=
  e.card = 2

/-- The closure condition for the two sides of a finite equality-constraint component. -/
def closedConstraintComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset (Finset V)) (π : V → Equiv.Perm V) : Prop :=
  (∀ e ∈ A, isSimpleEdge e) ∧
    (∀ f ∈ B, isSimpleEdge f) ∧
    (∀ e ∈ A, ∀ i : V, i ∉ e → e.image (π i) ∈ B) ∧
    (∀ f ∈ B, ∀ i : V, i ∉ f → f.image ((π i).symm) ∈ A)

/-- Every closed equality component balances its left and right edge variables. -/
def claim4449_componentBalance : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (A B : Finset (Finset V)) (π : V → Equiv.Perm V),
    3 ≤ Fintype.card V →
    (∀ i : V, (π i) i = i) →
    closedConstraintComponent A B π →
      A.card = B.card

/-- Finite square energy through channel N-1 in the real finite model. -/
def finiteSquareEnergy
    (F : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range N) (fun r =>
    x ^ r * (F r x) ^ 2 / (Nat.factorial r : ℝ))

/-- The energy after removing exceptional channel zero. -/
def higherChannelEnergy
    (F : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range N) (fun r =>
    x ^ (r + 1) * (F (r + 1) x) ^ 2 /
      (Nat.factorial (r + 1) : ℝ))

/-- The finite energy splits into its channel-zero term and higher channels. -/
def claim4467_energyDecomposition
    (F : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) : Prop :=
  finiteSquareEnergy F (N + 1) x =
    (F 0 x) ^ 2 + higherChannelEnergy F N x

end MathlibPlus.Open.ResearchFormalizationBatch.GraphAndEnergy
