import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0043

noncomputable section
open scoped BigOperators

abbrev BoundaryVariable := ℕ × ℕ
abbrev BoundaryPolynomial := MvPolynomial BoundaryVariable ℚ
abbrev ConeCoefficient := MvPolynomial ℕ ℚ
abbrev ConeClosure := Polynomial ConeCoefficient

/-- The graph obtained by adjoining the new vertex `none` to the old marks. -/
def coneGraph {V : Type*} (G : SimpleGraph V) (R : Finset V) :
    SimpleGraph (Option V) :=
  SimpleGraph.fromRel (fun u v =>
    match u, v with
    | none, some w => w ∈ R
    | some w, none => w ∈ R
    | some u, some v => G.Adj u v
    | none, none => False)

/-- The component monomial records both component order and marked count. -/
noncomputable def markedComponentMonomial {V : Type*} [Fintype V]
    (R : Finset V) (E : Finset (Sym2 V)) : BoundaryPolynomial :=
  letI := Classical.decEq V
  let H := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  ∏ C : H.ConnectedComponent,
    letI : Fintype C.supp := Fintype.ofFinite C.supp
    letI := Classical.decEq C.supp
    MvPolynomial.X
      (Fintype.card C.supp,
        (Finset.univ.filter (fun v : C.supp => (v : V) ∈ R)).card)

/-- The exact selected-edge boundary-block profile. -/
noncomputable def markedBoundaryProfile {V : Type*} [Fintype V]
    (G : SimpleGraph V) (R : Finset V) : BoundaryPolynomial :=
  letI := Classical.decEq V
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  ∑ E ∈ G.edgeFinset.powerset, markedComponentMonomial R E

/-- The displayed substitution `b_(a,j) ↦ x_a + (2^j-1)t^a`. -/
noncomputable def coneSubstitution : BoundaryPolynomial →+* ConeClosure :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ConeClosure) (fun a : BoundaryVariable =>
    Polynomial.C (MvPolynomial.X a.1) +
      ((2 : ℚ) ^ a.2 - 1) • (Polynomial.X ^ a.1))

/-- The coefficient-consuming map `Λ_z(t^k M)=(x_(k+1)+z^(k+1))M`. -/
noncomputable def coneLambda (H : ConeClosure) : ConeClosure :=
  ∑ k ∈ H.support,
    (Polynomial.C (MvPolynomial.X (k + 1)) + Polynomial.X ^ (k + 1)) *
      Polynomial.C (H.coeff k)

/-- One marked root specializes the boundary profile to the rooted factor. -/
noncomputable def rootedFactor {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : V) : ConeClosure :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ConeClosure) (fun a : BoundaryVariable =>
    Polynomial.C (MvPolynomial.X a.1) +
      if a.2 = 1 then Polynomial.X ^ a.1 else 0)
    (markedBoundaryProfile G {r})

/-- Claim 16110: cone closure is the boundary substitution followed by
coefficient consumption, with the rooted factor of the actual cone on the
left-hand side. -/
def claim16110 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (R : Finset V),
    rootedFactor (coneGraph G R) none =
      coneLambda (coneSubstitution (markedBoundaryProfile G R))

end
end MathlibPlus.Open.ResearchFormalization.BatchQ0043
