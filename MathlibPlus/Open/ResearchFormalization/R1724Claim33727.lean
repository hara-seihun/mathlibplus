import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1724Claim33727

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable section

abbrev XPoly := MvPolynomial ℕ ℚ
abbrev WPoly := Polynomial XPoly

/-- A finite rooted tree carrier, with its graph and distinguished root retained. -/
structure RootedTree where
  carrier : Type
  fintype : Fintype carrier
  graph : SimpleGraph carrier
  root : carrier
  isTree : graph.IsTree

/-- The order of a rooted tree. -/
def treeOrder (T : RootedTree) : ℕ :=
  @Fintype.card T.carrier T.fintype

/-- A nonempty block whose induced graph is connected. -/
def connectedBlock {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : Prop :=
  D.Nonempty ∧ (G.induce (D : Set V)).Connected

/-- A partition of a specified vertex set into disjoint connected blocks. -/
def connectedPartition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (π : Finset (Finset V)) : Prop :=
  π.biUnion id = S ∧
    (∀ D ∈ π, D.Nonempty ∧ D ⊆ S ∧ connectedBlock G D) ∧
    (∀ D ∈ π, ∀ E ∈ π, D ≠ E → Disjoint D E)

/-- The kept set is root-connected, with the empty kept set allowed. -/
def rootConnectedSet (T : RootedTree) (Q : Finset T.carrier) : Prop :=
  Q = ∅ ∨
    (T.root ∈ Q ∧
      (T.graph.induce (Q : Set T.carrier)).Connected)

/-- The monomial recording the sizes of all deleted connected blocks. -/
def blockMonomial {V : Type*}
    (π : Finset (Finset V)) : XPoly :=
  ∏ D ∈ π, MvPolynomial.X D.card

/-- The exact rooted-tree pruning factor at a named order n. -/
noncomputable def pruningFormula (T : RootedTree) (n : ℕ) : WPoly :=
  letI := T.fintype
  ∑ Q : Finset T.carrier, ∑ π : Finset (Finset T.carrier),
    if rootConnectedSet T Q ∧ connectedPartition T.graph Qᶜ π then
      Polynomial.X ^ (n - Q.card) * Polynomial.C (blockMonomial π)
    else 0

/-- The rooted-tree polynomial `Π_{B,r}`. -/
noncomputable def pruningFactor (T : RootedTree) : WPoly :=
  pruningFormula T (treeOrder T)

/-- The product `P_C` over a multiset of rooted trees. -/
noncomputable def pruningProduct (C : Multiset RootedTree) : WPoly :=
  (C.map pruningFactor).prod

/-- The row `R_k(C)=[w^k]P_C`. -/
def row (k : ℕ) (C : Multiset RootedTree) : XPoly :=
  (pruningProduct C).coeff k

/-- The marked row `M_k(C)=∂_{x₁}R_k(C)`. -/
def markedRow (k : ℕ) (C : Multiset RootedTree) : XPoly :=
  MvPolynomial.pderiv 1 (row k C)

/-- The total weight `W(C)`. -/
def totalWeight (C : Multiset RootedTree) : ℕ :=
  (C.map treeOrder).sum

/-- Claim 33727: the kept-set/connected-block pruning factor and the
multiset product, coefficient rows, marked rows, and total weight are exactly
the stated constructions. -/
def claim33727 : Prop :=
  (∀ (T : RootedTree) (n : ℕ),
    treeOrder T = n → pruningFactor T = pruningFormula T n) ∧
    (∀ (C : Multiset RootedTree),
      pruningProduct C = (C.map pruningFactor).prod) ∧
    (∀ (C : Multiset RootedTree) (k : ℕ),
      row k C = (pruningProduct C).coeff k ∧
        markedRow k C = MvPolynomial.pderiv 1 (row k C)) ∧
    (∀ (C : Multiset RootedTree),
      totalWeight C = (C.map treeOrder).sum)

end

end MathlibPlus.Open.ResearchFormalization.R1724Claim33727
