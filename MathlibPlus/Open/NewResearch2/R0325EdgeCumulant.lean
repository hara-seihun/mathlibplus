import MathlibPlus.Open.Graphs.BasisTranspose
import MathlibPlus.Open.Research.TreeCuts

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0325EdgeCumulant

noncomputable section
open Classical

private abbrev GraphShape :=
  Σ n : ℕ, MathlibPlus.Open.Graphs.GraphIsoClass n

private noncomputable def componentShape
    {V : Type} [Fintype V]
    (T : SimpleGraph V) (p : Setoid V) (q : Quotient p) : GraphShape :=
  let C := {v : V // Quotient.mk' v = q}
  let e := Fintype.equivFin C
  ⟨Fintype.card C,
    MathlibPlus.Open.Graphs.graphClass
      (SimpleGraph.comap e.symm
        (T.induce {v : V | Quotient.mk' v = q}))⟩

private noncomputable def deletedPartition
    {V : Type} [Fintype V]
    (T : SimpleGraph V) (S : Finset (Sym2 V)) : Setoid V :=
  Relation.EqvGen.setoid
    (fun a b : V => T.Adj a b ∧ Sym2.mk a b ∉ (S : Set (Sym2 V)))

private noncomputable def forestCumulantProduct
    {V : Type} [Fintype V]
    (T : SimpleGraph V) (S : Finset (Sym2 V)) :
    MvPolynomial GraphShape ℤ :=
  let p := deletedPartition T S
  ∏ q : Quotient p, MvPolynomial.X (componentShape T p q)

private noncomputable def cutSets
    {V : Type} [Fintype V]
    (T : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  (Finset.univ : Finset (Finset (Sym2 V))).filter
    (fun S => ∀ e ∈ S, e ∈ T.edgeSet)

private noncomputable def treeCumulantExpansion
    {V : Type} [Fintype V]
    (T : SimpleGraph V) : MvPolynomial GraphShape ℤ :=
  (cutSets T).sum (fun S => forestCumulantProduct T S)

private noncomputable def properCumulantLayerTwo
    {V : Type} [Fintype V]
    (T : SimpleGraph V) : MvPolynomial GraphShape ℤ :=
  MvPolynomial.homogeneousComponent 2 (treeCumulantExpansion T)

private noncomputable def edgeCumulantProduct
    {V : Type} [Fintype V]
    (T : SimpleGraph V) (e : Sym2 V) : MvPolynomial GraphShape ℤ :=
  forestCumulantProduct T {e}

/-- Claim 19879: the second proper cumulant layer is the sum of the products of
shape-refined connected cumulants of the two components obtained from each tree
edge deletion. -/
def claim19879 : Prop :=
  ∀ {V : Type} [Fintype V] (T : SimpleGraph V), T.IsTree →
    properCumulantLayerTwo T =
      (MathlibPlus.Open.Research.TreeCuts.graphEdges T).sum
        (fun e => edgeCumulantProduct T e)

end
end MathlibPlus.Open.NewResearch2.R0325EdgeCumulant
