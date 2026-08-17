import MathlibPlus.GraphTheory.Claim28295

namespace MathlibPlus.Open.ResearchFormalization.R0608Corolla

open scoped BigOperators

noncomputable section

private abbrev OrdinaryPowerSums := MvPolynomial ℕ ℚ
private abbrev RootedPowerSums := MvPolynomial (Sum ℕ Unit) ℚ

private def powerIndex (m : ℕ) : Sum ℕ Unit := Sum.inl m
private def rootIndex : Sum ℕ Unit := Sum.inr ()

private noncomputable def selectedGraph
    {V : Type*} (S : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

private noncomputable def componentPowerProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : OrdinaryPowerSums := by
  classical
  exact (MathlibPlus.GraphTheory.Claim28295.componentSizes H).map
      (fun k => MvPolynomial.X k) |>.prod

private noncomputable def componentPowerProductRooted
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : RootedPowerSums := by
  classical
  exact (MathlibPlus.GraphTheory.Claim28295.componentSizes H).map
      (fun k => MvPolynomial.X (powerIndex k)) |>.prod

private noncomputable def rootComponentSize
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (r : V) : ℕ := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  exact (H.connectedComponentMk r).supp.ncard

private noncomputable def nonrootPowerProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (r : V) : RootedPowerSums := by
  classical
  let sizes := MathlibPlus.GraphTheory.Claim28295.componentSizes H
  exact (sizes.erase (rootComponentSize H r)).map
      (fun k => MvPolynomial.X (powerIndex k)) |>.prod

/-- The ordinary tree chromatic symmetric function in its signed component
(power-sum) expansion. -/
private noncomputable def treeCSF
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : OrdinaryPowerSums := by
  classical
  exact ∑ S ∈ T.edgeFinset.powerset,
    MvPolynomial.C ((-1 : ℚ) ^ S.card) *
      componentPowerProduct (selectedGraph S)

/-- The rooted open response uses a variable disjoint from all power sums. -/
private noncomputable def rootedOpenResponse
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (r : V) : RootedPowerSums := by
  classical
  exact ∑ S ∈ T.edgeFinset.powerset,
    MvPolynomial.C ((-1 : ℚ) ^ S.card) *
      MvPolynomial.X rootIndex ^ rootComponentSize (selectedGraph S) r *
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
    (T : SimpleGraph V) : RootedPowerSums := by
  classical
  exact ∑ k ∈ Finset.Icc 1 (Fintype.card V),
    MvPolynomial.C (k : ℚ) * MvPolynomial.X rootIndex ^ k *
      embedPowerSums (MvPolynomial.pderiv k (treeCSF T))

private noncomputable def graftCorolla
    {V : Type*} (T : SimpleGraph V) (v : V) (q : ℕ) :
    SimpleGraph (V ⊕ Fin q) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => T.Adj a b
    | Sum.inl a, Sum.inr _ => a = v
    | Sum.inr _, Sum.inl b => b = v
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro x y h
    rcases x with a | i <;> rcases y with b | j
    · exact T.symm.symm _ _ h
    · exact h
    · exact h
    · exact h.elim
  ⟩
  loopless := ⟨by
    intro x
    cases x with
    | inl a => exact T.loopless.irrefl a
    | inr j => simp
  ⟩

private noncomputable def corollaCSF
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (T : SimpleGraph V) : OrdinaryPowerSums :=
  ∑ v : V, treeCSF (graftCorolla T v q)

private noncomputable def positiveWitt
    (j : ℕ) (P : OrdinaryPowerSums) : OrdinaryPowerSums := by
  classical
  exact ∑ m ∈ P.vars.filter (fun m => 1 ≤ m),
    MvPolynomial.C (m : ℚ) * MvPolynomial.X (m + j) * MvPolynomial.pderiv m P

private noncomputable def firstDerivativeCombination
    (q : ℕ) (P : OrdinaryPowerSums) : OrdinaryPowerSums := by
  classical
  exact ∑ j ∈ Finset.range (q + 1),
    MvPolynomial.C (((-1 : ℚ) ^ j) * (Nat.choose q j : ℚ)) *
      MvPolynomial.X 1 ^ (q - j) * positiveWitt j P

private noncomputable def Lq
    (q : ℕ) : OrdinaryPowerSums → OrdinaryPowerSums :=
  firstDerivativeCombination q

/-- Claim 26370: the actual sum of the CSFs of the one-leaf grafts is the
first-corolla power-sum derivative formula. -/
def firstCorollaOperatorFormula_claim26370 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V),
    T.IsTree →
      corollaCSF 1 T =
        MvPolynomial.C (Fintype.card V : ℚ) * MvPolynomial.X 1 * treeCSF T -
          ∑ m ∈ Finset.Icc 1 (Fintype.card V),
            MvPolynomial.C (m : ℚ) * MvPolynomial.X (m + 1) *
              MvPolynomial.pderiv m (treeCSF T)

/-- Claim 26372: the explicitly defined target operators are universal finite
linear combinations of first power-sum derivatives, intertwine with the
actual pendant-corolla grafting, and the resulting tower is already fixed by
(the equivalent) full rooted first jet. -/
def corollaTowerDeterminedByFirstJet_claim26372 : Prop :=
  ∀ {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (T : SimpleGraph V) (U : SimpleGraph W),
    T.IsTree → U.IsTree →
      (∀ q : ℕ,
        corollaCSF q T = Lq q (treeCSF T)) ∧
      rootedOrbitSum T = firstJetFormula T ∧
      rootedOrbitSum U = firstJetFormula U ∧
      (treeCSF T = treeCSF U ↔ rootedOrbitSum T = rootedOrbitSum U) ∧
      (rootedOrbitSum T = rootedOrbitSum U →
        ∀ q : ℕ, corollaCSF q T = corollaCSF q U)

end
end MathlibPlus.Open.ResearchFormalization.R0608Corolla
