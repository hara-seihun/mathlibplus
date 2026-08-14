import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.ComponentCollapse

abbrev Scalar := Polynomial (Polynomial ℚ)
abbrev ComponentForest := Multiplicative (Multiset ℕ)

noncomputable def z : Scalar := Polynomial.C Polynomial.X
noncomputable def x₁ : Scalar := Polynomial.X
noncomputable def s : Scalar := z + x₁

noncomputable def scalarCollapse (a : ℕ → ℚ) (F : ComponentForest) : Scalar :=
  ((Multiplicative.toAdd F).map
    (fun k => Polynomial.C (Polynomial.C (a k)) * s ^ k)).prod

noncomputable def collapseLinear (a : ℕ → ℚ)
    (u : MonoidAlgebra ℚ ComponentForest) : Scalar :=
  Finsupp.sum u.coeff
    (fun F q => Polynomial.C (Polynomial.C q) * scalarCollapse a F)

def claim_26408 : Prop :=
  ∀ (a : ℕ → ℚ) (k : ℕ) (F G : ComponentForest),
    scalarCollapse a (Multiplicative.ofAdd ({k} : Multiset ℕ)) =
      Polynomial.C (Polynomial.C (a k)) * s ^ k ∧
    scalarCollapse a (F * G) = scalarCollapse a F * scalarCollapse a G

noncomputable def edgeSubsets {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Finset (Finset (Sym2 V)) := by
  classical
  exact (Finset.univ : Finset (Sym2 V)).powerset.filter
    (fun A => ∀ e ∈ A, e ∈ T.edgeSet)

noncomputable def selectedGraph {V : Type*}
    (T : SimpleGraph V) (A : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => T.Adj v w ∧ Sym2.mk v w ∈ A)

noncomputable def componentSize {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : G.ConnectedComponent) : ℕ := by
  classical
  exact Fintype.card {v : V // G.connectedComponentMk v = C}

noncomputable def componentForest {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ComponentForest :=
  Multiplicative.ofAdd
    ((Finset.univ : Finset G.ConnectedComponent).val.map (componentSize G))

noncomputable def unrootedU {V : Type*} [Fintype V]
    (T : SimpleGraph V) : MonoidAlgebra ℚ ComponentForest := by
  classical
  exact Finset.sum (edgeSubsets T)
    (fun A => MonoidAlgebra.single (componentForest (selectedGraph T A)) 1)

noncomputable def componentWeight {V : Type*} [Fintype V]
    (a : ℕ → ℚ) (G : SimpleGraph V) : Scalar :=
  ∏ C : G.ConnectedComponent,
    Polynomial.C (Polynomial.C (a (componentSize G C)))

def claim_26409 : Prop :=
  ∀ {V : Type*} [Fintype V] (T : SimpleGraph V) (a : ℕ → ℚ),
    T.IsTree →
      collapseLinear a (unrootedU T) =
        s ^ Fintype.card V *
          Finset.sum (edgeSubsets T) (fun A => componentWeight a (selectedGraph T A))

def claim_26410 : Prop :=
  ∀ {V : Type*} [Fintype V] (T : SimpleGraph V) (α : ℚ),
    T.IsTree →
      collapseLinear (fun _ => α) (unrootedU T) =
        Polynomial.C (Polynomial.C (α * (1 + α) ^ (Fintype.card V - 1))) *
          s ^ Fintype.card V

end MathlibPlus.Open.Research.ComponentCollapse
