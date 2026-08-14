import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0849

noncomputable section

open scoped BigOperators

/-- A connected vertex set of a finite simple graph. -/
def connectedVertexSet {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ (F.induce (A : Set V)).Connected

/-- An unordered collection of pairwise vertex-disjoint connected sets of size
at least two. -/
def connectedPacking {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (r : ℕ) (C : Finset (Finset V)) : Prop :=
  C.card = r ∧
    (C : Set (Finset V)).Pairwise (fun A B => Disjoint A B) ∧
    ∀ A, A ∈ C → 2 ≤ A.card ∧ connectedVertexSet F A

/-- The finite carrier of all connected packings of a fixed size. -/
def connectedPackings {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (r : ℕ) : Finset (Finset (Finset V)) := by
  classical
  exact Finset.univ.filter (connectedPacking F r)

/-- The monomial attached to a packing, with x at variable 0 and z_k at
variable k. -/
def connectedPackingMonomial {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (Finset V)) : MvPolynomial ℕ ℚ :=
  let N := Fintype.card V
  (MvPolynomial.X 0) ^
      (N - ∑ A ∈ C, A.card) *
    ∏ A ∈ C, MvPolynomial.X A.card

/-- The connected-packing coefficient K_{F,r}. -/
def connectedPackingCoefficient {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (r : ℕ) : MvPolynomial ℕ ℚ := by
  classical
  exact ∑ C ∈ connectedPackings F r, connectedPackingMonomial C

/-- The exact collection and coefficient definitions for connected packings. -/
def connectedPackingCoefficientDefinition : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (r : ℕ),
    F.IsAcyclic →
    (∀ C : Finset (Finset V),
      C ∈ connectedPackings F r ↔ connectedPacking F r C) ∧
    connectedPackingCoefficient F r =
      ∑ C ∈ connectedPackings F r, connectedPackingMonomial C

/-- The universal empty row and the x-degree descent of every positive row. -/
def universalConstantRowAndStrictDegreeDescent : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V),
    F.IsAcyclic →
    connectedPackingCoefficient F 0 =
        (MvPolynomial.X 0) ^ Fintype.card V ∧
    ∀ r : ℕ, 0 < r →
      MvPolynomial.degreeOf 0 (connectedPackingCoefficient F r) ≤
          Fintype.card V - 2 * r ∧
      MvPolynomial.degreeOf 0 (connectedPackingCoefficient F r) <
          Fintype.card V

end

end MathlibPlus.Open.ResearchFormalization.R0849
