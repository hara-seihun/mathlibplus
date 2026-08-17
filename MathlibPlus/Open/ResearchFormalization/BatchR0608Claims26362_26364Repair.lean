import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0608Claims

noncomputable section

private abbrev Coeff := MvPolynomial ℕ ℚ
private abbrev Response := Polynomial Coeff

private def selectedEdgeGraph {V : Type*}
    (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => s(v, w) ∈ F)

private noncomputable def componentProduct {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Coeff := by
  classical
  exact ∏ C : G.ConnectedComponent, MvPolynomial.X C.supp.ncard

private noncomputable def nonrootComponentProduct
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : V) : Coeff := by
  classical
  let root := G.connectedComponentMk r
  exact ∏ C ∈ (Finset.univ.filter (fun C : G.ConnectedComponent => C ≠ root)),
    MvPolynomial.X C.supp.ncard

private noncomputable def chromaticPowerSum
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Coeff := by
  classical
  exact ∑ F ∈ T.edgeFinset.powerset,
    (-1 : Coeff) ^ F.card * componentProduct (selectedEdgeGraph F)

private noncomputable def rootedOpenResponse
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (r : V) : Response := by
  classical
  exact ∑ F ∈ T.edgeFinset.powerset,
    (-1 : Response) ^ F.card *
      Polynomial.X ^
          ((selectedEdgeGraph F).connectedComponentMk r).supp.ncard *
      Polynomial.C (nonrootComponentProduct (selectedEdgeGraph F) r)

private noncomputable def rootedBranchFactor
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (r : V) : Response :=
  Polynomial.C (chromaticPowerSum T) - rootedOpenResponse T r

private noncomputable def rootedResponseSum
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Response :=
  ∑ r : V, rootedOpenResponse T r

private noncomputable def rootedFirstJet
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Response := by
  classical
  exact ∑ k ∈ Finset.range (Fintype.card V + 1),
    Polynomial.X ^ k *
      Polynomial.C
        (MvPolynomial.C (k : ℚ) *
          MvPolynomial.pderiv k (chromaticPowerSum T))

/-- Claim 26362: equality of the exact signed rooted open responses on finite
unrooted trees forces a rooted graph isomorphism. -/
def claim26362_signedRootedResponseDistinguishesTrees : Prop :=
  ∀ {n m : ℕ}
    (T : SimpleGraph (Fin n)) (U : SimpleGraph (Fin m))
    (r : Fin n) (s : Fin m),
    T.IsTree →
    U.IsTree →
    rootedOpenResponse T r = rootedOpenResponse U s →
      ∃ e : T.Adj ≃r U.Adj, e r = s

/-- Claim 26363: the exact closed branch factor has the stated z=0
specialization, recovers the open response, and distinguishes rooted trees. -/
def claim26363_branchFactorDistinguishesTrees : Prop :=
  ∀ {n m : ℕ}
    (T : SimpleGraph (Fin n)) (U : SimpleGraph (Fin m))
    (r : Fin n) (s : Fin m),
    T.IsTree →
    U.IsTree →
    rootedBranchFactor T r = rootedBranchFactor U s →
      (rootedBranchFactor T r).eval 0 = chromaticPowerSum T ∧
      rootedOpenResponse T r =
        Polynomial.C ((rootedBranchFactor T r).eval 0) -
          rootedBranchFactor T r ∧
      ∃ e : T.Adj ≃r U.Adj, e r = s

/-- Claim 26364: summing the exact rooted responses gives the full first jet
of the ordinary power-sum chromatic symmetric function. -/
def claim26364_fullFirstJetRootedResponseSum : Prop :=
  ∀ {n : ℕ} (T : SimpleGraph (Fin n)),
    T.IsTree →
      rootedResponseSum T = rootedFirstJet T

end

end MathlibPlus.Open.ResearchFormalization.BatchR0608Claims
