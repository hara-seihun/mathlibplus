import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.R1556

/-- Finite root-containing connected vertex sets of a rooted graph. -/
def rootConnectedFinsets {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : V) :=
  {W : Finset V // r ∈ W ∧ (G.induce (W : Set V)).Connected}

/-- The graph obtained by joining two disjoint graphs by their two rooted vertices. -/
def joinedGraph {V U : Type*}
    (R : SimpleGraph V) (T : SimpleGraph U) (r : V) (t : U) :
    SimpleGraph (V ⊕ U) where
  Adj x y :=
    match x, y with
    | Sum.inl v, Sum.inl w => R.Adj v w
    | Sum.inr v, Sum.inr w => T.Adj v w
    | Sum.inl v, Sum.inr w => v = r ∧ w = t
    | Sum.inr v, Sum.inl w => v = t ∧ w = r
  symm := Std.Symm.mk (by
    intro x y h
    cases x with
    | inl v =>
        cases y with
        | inl w => exact R.symm.symm v w h
        | inr w => exact ⟨h.2, h.1⟩
    | inr v =>
        cases y with
        | inl w => exact ⟨h.2, h.1⟩
        | inr w => exact T.symm.symm v w h)
  loopless := Std.Irrefl.mk (by
    intro x
    cases x with
    | inl v => exact R.loopless.irrefl v
    | inr v => exact T.loopless.irrefl v)

/-- Connected finite sets meeting both sides of the joining edge. -/
def crossingConnectedFinsets {V U : Type*} [Fintype V] [Fintype U]
    (R : SimpleGraph V) (T : SimpleGraph U) (r : V) (t : U) :=
  {W : Finset (V ⊕ U) //
    (∃ v : V, Sum.inl v ∈ W) ∧
    (∃ u : U, Sum.inr u ∈ W) ∧
    ((joinedGraph R T r t).induce (W : Set (V ⊕ U))).Connected}

/-- The rooted connected-set generating polynomial. -/
noncomputable def rootedConnectedPolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : V) : Polynomial ℕ := by
  classical
  letI : DecidableEq V := Classical.decEq V
  letI : Fintype (Finset V) := inferInstance
  exact ∑ W : Finset V,
    if r ∈ W ∧ (G.induce (W : Set V)).Connected then
      Polynomial.X ^ W.card else 0

/-- The crossing connected-set generating polynomial. -/
noncomputable def crossingConnectedPolynomial
    {V U : Type*} [Fintype V] [Fintype U]
    (R : SimpleGraph V) (T : SimpleGraph U) (r : V) (t : U) : Polynomial ℕ := by
  classical
  letI : DecidableEq V := Classical.decEq V
  letI : DecidableEq U := Classical.decEq U
  letI : Fintype (Finset (V ⊕ U)) := inferInstance
  exact ∑ W : Finset (V ⊕ U),
    if (∃ v : V, Sum.inl v ∈ W) ∧
        (∃ u : U, Sum.inr u ∈ W) ∧
        ((joinedGraph R T r t).induce (W : Set (V ⊕ U))).Connected then
      Polynomial.X ^ W.card else 0

/-- Statement 36 of the admitted rooted-tree packet. -/
def claim_37836 : Prop :=
  ∀ (V U : Type*) [Fintype V] [Fintype U]
    (R : SimpleGraph V) (T : SimpleGraph U) (r : V) (t : U),
    R.IsTree → T.IsTree →
      Nonempty
          (crossingConnectedFinsets R T r t ≃
            rootConnectedFinsets R r × rootConnectedFinsets T t) ∧
      crossingConnectedPolynomial R T r t =
        rootedConnectedPolynomial R r * rootedConnectedPolynomial T t ∧
      Polynomial.Monic (rootedConnectedPolynomial R r) ∧
        (rootedConnectedPolynomial R r).natDegree = Fintype.card V ∧
      Polynomial.Monic (rootedConnectedPolynomial T t) ∧
        (rootedConnectedPolynomial T t).natDegree = Fintype.card U

end MathlibPlus.Open.R1556
