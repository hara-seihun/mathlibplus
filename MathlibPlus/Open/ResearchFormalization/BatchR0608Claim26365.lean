import MathlibPlus.GraphTheory.Claim28295

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchR0608Claim26365

attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev OrdinaryPowerSums := MvPolynomial ℕ ℚ
private abbrev RootedPowerSums := MvPolynomial (Sum ℕ Unit) ℚ

private def powerIndex (m : ℕ) : Sum ℕ Unit := Sum.inl m
private def rootIndex : Sum ℕ Unit := Sum.inr ()

private def selectedGraph {V : Type*} (S : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

private noncomputable def componentPowerProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : OrdinaryPowerSums :=
  ((MathlibPlus.GraphTheory.Claim28295.componentSizes H).map
      (fun k => MvPolynomial.X k)).prod

private noncomputable def rootComponentSize
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (r : V) : ℕ :=
  (H.connectedComponentMk r).supp.ncard

private noncomputable def nonrootPowerProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (r : V) : RootedPowerSums :=
  (((MathlibPlus.GraphTheory.Claim28295.componentSizes H).erase
      (rootComponentSize H r)).map
      (fun k => MvPolynomial.X (powerIndex k))).prod

private noncomputable def treeCSF
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : OrdinaryPowerSums :=
  ∑ S ∈ T.edgeFinset.powerset,
    MvPolynomial.C ((-1 : ℚ) ^ S.card) *
      componentPowerProduct (selectedGraph S)

private noncomputable def rootedOpenResponse
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (r : V) : RootedPowerSums :=
  ∑ S ∈ T.edgeFinset.powerset,
    MvPolynomial.C ((-1 : ℚ) ^ S.card) *
      MvPolynomial.X rootIndex ^
        (rootComponentSize (selectedGraph S) r) *
      nonrootPowerProduct (selectedGraph S) r

private noncomputable def rootedOrbitSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : RootedPowerSums :=
  ∑ r : V, rootedOpenResponse T r

private noncomputable def embedPowerSums
    (P : OrdinaryPowerSums) : RootedPowerSums :=
  MvPolynomial.rename powerIndex P

private noncomputable def firstJetFormula
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : RootedPowerSums :=
  ∑ k ∈ Finset.Icc 1 (Fintype.card V),
    MvPolynomial.C (k : ℚ) * MvPolynomial.X rootIndex ^ k *
      embedPowerSums (MvPolynomial.pderiv k (treeCSF T))

private def eraseRootToOrdinary
    (m : (Sum ℕ Unit) →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapDomain
    (fun i => match i with
      | Sum.inl k => k
      | Sum.inr _ => 0)
    (m.erase rootIndex)

private noncomputable def weightedEulerTerm
    (P : RootedPowerSums) (m : (Sum ℕ Unit) →₀ ℕ) : OrdinaryPowerSums :=
  MvPolynomial.C (P.coeff m) *
      MvPolynomial.X (m rootIndex) *
    MvPolynomial.monomial (eraseRootToOrdinary m) 1

private noncomputable def weightedEulerContraction
    (P : RootedPowerSums) (n : ℕ) : OrdinaryPowerSums :=
  (n : ℚ)⁻¹ •
    ∑ m ∈ P.support, weightedEulerTerm P m

/-- The first-jet equality and its weighted Euler recovery are asserted on the
same finite-tree carriers; the final equivalence is only for unrooted trees. -/
def fullFirstJetAndTreeCSFInformation_claim26365 : Prop :=
  ∀ {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (T : SimpleGraph V) (U : SimpleGraph W),
    T.IsTree → U.IsTree →
      weightedEulerContraction (rootedOrbitSum T) (Fintype.card V) =
          treeCSF T ∧
      weightedEulerContraction (rootedOrbitSum U) (Fintype.card W) =
          treeCSF U ∧
      rootedOrbitSum T = firstJetFormula T ∧
      rootedOrbitSum U = firstJetFormula U ∧
      (treeCSF T = treeCSF U ↔
        rootedOrbitSum T = rootedOrbitSum U)

end MathlibPlus.Open.ResearchFormalization.BatchR0608Claim26365
