import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Q0057

open scoped BigOperators

noncomputable section

/-- Variable names for the `x_i`, `z_i`, and the common `y` in the higher GDP. -/
private abbrev GDPVar (m : ℕ) := Fin m ⊕ (Fin m ⊕ Unit)

private def xVar (m : ℕ) (i : Fin m) : MvPolynomial (GDPVar m) ℕ :=
  MvPolynomial.X (Sum.inl i)

private def zVar (m : ℕ) (i : Fin m) : MvPolynomial (GDPVar m) ℕ :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

private def yVar (m : ℕ) : MvPolynomial (GDPVar m) ℕ :=
  MvPolynomial.X (Sum.inr (Sum.inr Unit.unit))

/-- The internal edge count of a vertex set in a finite simple graph. -/
private noncomputable def internalEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (A : Finset V) : ℕ := by
  classical
  exact Fintype.card {p : V × V // p.1 ∈ A ∧ p.2 ∈ A ∧ F.Adj p.1 p.2} / 2

/-- The state of a vertex: `none` is the residual state `A₀`. -/
private noncomputable def stateOf {V : Type*} [DecidableEq V] {m : ℕ}
    (A : Fin m → Finset V) (v : V) : Option (Fin m) :=
  if h : ∃ i, v ∈ A i then some (Classical.choose h) else none

/-- Pairwise disjointness of the selected vertex sets. -/
private def pairwiseDisjoint {V : Type*} [DecidableEq V] {m : ℕ}
    (A : Fin m → Finset V) : Prop :=
  ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (A i) (A j)

/-- The number of edges whose endpoint states differ, including the residual state. -/
private noncomputable def crossingEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (F : SimpleGraph V) (A : Fin m → Finset V) : ℕ := by
  classical
  exact Fintype.card
      {p : V × V // F.Adj p.1 p.2 ∧ stateOf A p.1 ≠ stateOf A p.2} / 2

/-- One summand in the higher generalized-degree polynomial. -/
private noncomputable def gdpTerm {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (m : ℕ) (A : Fin m → Finset V) :
    MvPolynomial (GDPVar m) ℕ :=
  (∏ i : Fin m,
      xVar m i ^ (A i).card * zVar m i ^ internalEdgeCount F (A i)) *
    yVar m ^ crossingEdgeCount F A

/-- The explicit sum over disjoint, nonnecessarily exhaustive state sets. -/
private noncomputable def higherGDPExpansion {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (m : ℕ) : MvPolynomial (GDPVar m) ℕ := by
  classical
  exact ∑ A : Fin m → Finset V,
    if pairwiseDisjoint A then gdpTerm F m A else 0

/-- Ordinary GDP has a collision among finite trees. -/
def ordinaryGDPDoesNotDistinguishTrees : Prop :=
  ∃ n : ℕ, ∃ T T' : SimpleGraph (Fin n),
    T.IsTree ∧ T'.IsTree ∧
      higherGDPExpansion T 1 = higherGDPExpansion T' 1 ∧
      ¬ Nonempty (T ≃g T')

end
end MathlibPlus.Open.ResearchFormalization.Q0057
