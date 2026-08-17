import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0608RootedResponseOrientation

noncomputable section

open scoped BigOperators Sym2
attribute [local instance] Classical.propDecidable Classical.decEq

private def properColoringCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Fintype.card {c : V → Fin k //
    ∀ e : G.edgeSet,
      Sym2.lift (⟨fun v w => c v ≠ c w, by simp [ne_comm]⟩) e.1}

private def deletedGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  G.induce {v : V | v ∉ S}

private def inducedGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.induce (S : Set V)

private def rootedTwoAlphabetChromatic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ) : ℕ :=
  ∑ S ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ r)).powerset,
    properColoringCount (deletedGraph G S) A.card *
      properColoringCount (inducedGraph G S) B.card

/-- The crossing companion stores the second character on the root-containing
complement of the selected subset. -/
private def rootCrossingCompanion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (B : Finset ℕ) : Finset V → ℕ :=
  fun S => properColoringCount (deletedGraph G S) B.card

private def scalarEvaluateRootCrossing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ) : ℕ :=
  ∑ S ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ r)).powerset,
    properColoringCount (inducedGraph G S) A.card *
      rootCrossingCompanion G r B S

private abbrev Coeff := MvPolynomial ℕ ℚ
private abbrev Response := Polynomial Coeff

private def selectedEdgeGraph {V : Type*}
    (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => s(v, w) ∈ F)

private noncomputable def componentProduct {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Coeff :=
  ∏ C : G.ConnectedComponent, MvPolynomial.X C.supp.ncard

private noncomputable def nonrootComponentProduct
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : V) : Coeff :=
  let root := G.connectedComponentMk r
  ∏ C ∈ (Finset.univ.filter
    (fun C : G.ConnectedComponent => C ≠ root)),
    MvPolynomial.X C.supp.ncard

private noncomputable def chromaticPowerSum
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Coeff :=
  ∑ F ∈ T.edgeFinset.powerset,
    (-1 : Coeff) ^ F.card * componentProduct (selectedEdgeGraph F)

private noncomputable def rootedOpenResponse
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (r : V) : Response :=
  ∑ F ∈ T.edgeFinset.powerset,
    (-1 : Response) ^ F.card *
      Polynomial.X ^
        (((selectedEdgeGraph F).connectedComponentMk r).supp.ncard) *
      Polynomial.C (nonrootComponentProduct (selectedEdgeGraph F) r)

private noncomputable def rootedBranchFactor
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (r : V) : Response :=
  Polynomial.C (chromaticPowerSum T) - rootedOpenResponse T r

/-- Claim 26358: with the crossing companion oriented so that its stored
second character occupies the root-containing side, scalar evaluation by A is
exactly the swapped rooted orientation X^bullet[B|A]. -/
def claim26358 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ),
    Disjoint A B →
      scalarEvaluateRootCrossing G r A B =
        rootedTwoAlphabetChromatic G r B A

/-- Claim 26359: the signed selected-edge root response uses the component of
r in the selected-edge graph, and H is its closed branch factor X_T-O_T,r. -/
def claim26359 : Prop :=
  ∀ {n : ℕ} (T : SimpleGraph (Fin n)) (r : Fin n),
    T.IsTree →
      rootedBranchFactor T r =
          Polynomial.C (chromaticPowerSum T) - rootedOpenResponse T r ∧
        rootedOpenResponse T r =
          ∑ F ∈ T.edgeFinset.powerset,
            (-1 : Response) ^ F.card *
              Polynomial.X ^
                (((selectedEdgeGraph F).connectedComponentMk r).supp.ncard) *
              Polynomial.C
                (nonrootComponentProduct (selectedEdgeGraph F) r)

/-- Claim 26362: equality of the exact signed rooted responses on finite trees
forces an isomorphism carrying the distinguished root to the distinguished
root. -/
def claim26362 : Prop :=
  ∀ {n m : ℕ}
    (T : SimpleGraph (Fin n)) (U : SimpleGraph (Fin m))
    (r : Fin n) (s : Fin m),
    T.IsTree → U.IsTree →
      rootedOpenResponse T r = rootedOpenResponse U s →
        ∃ e : T.Adj ≃r U.Adj, e r = s

end

end MathlibPlus.Open.NewResearch2.R0608RootedResponseOrientation
