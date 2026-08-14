import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

section BoundaryPolynomials

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev BoundaryPolynomial := Polynomial (Polynomial ℤ)

def boundaryU : BoundaryPolynomial :=
  Polynomial.X

def boundaryV : BoundaryPolynomial :=
  Polynomial.C Polynomial.X

def boundaryDegree (G : SimpleGraph V) (r : V) : Nat := by
  classical
  exact (Finset.univ.filter (fun x => G.Adj r x)).card

def connectedFinset (G : SimpleGraph V) (S : Finset V) : Prop :=
  SimpleGraph.Connected (G.induce (S : Set V))

def boundaryCount (G : SimpleGraph V) (S : Finset V) : Nat := by
  classical
  exact
    (Finset.univ.filter (fun y => y ∉ S ∧ ∃ x ∈ S, G.Adj x y)).card

def boundaryTerm (G : SimpleGraph V) (S : Finset V) : BoundaryPolynomial :=
  boundaryU ^ (S.card - 1) * boundaryV ^ boundaryCount G S

noncomputable def rootedBoundaryPolynomial
    (G : SimpleGraph V) (r : V) : BoundaryPolynomial := by
  classical
  exact ∑ S : Finset V,
    if S.Nonempty ∧ connectedFinset G S ∧ r ∈ S then
      boundaryTerm G S
    else 0

noncomputable def rootedBoundaryNontrivial
    (G : SimpleGraph V) (r : V) : BoundaryPolynomial := by
  classical
  exact ∑ S : Finset V,
    if 2 ≤ S.card ∧ connectedFinset G S ∧ r ∈ S then
      boundaryTerm G S
    else 0

noncomputable def unrootedBoundaryPolynomial
    (G : SimpleGraph V) : BoundaryPolynomial := by
  classical
  exact ∑ S : Finset V,
    if 2 ≤ S.card ∧ connectedFinset G S then
      boundaryTerm G S
    else 0

def rootedBoundaryReduced (G : SimpleGraph V) (r : V) : BoundaryPolynomial :=
  rootedBoundaryPolynomial G r - boundaryV ^ boundaryDegree G r

def rootedBoundaryCurrent (G : SimpleGraph V) (r : V) : BoundaryPolynomial :=
  unrootedBoundaryPolynomial G +
    (boundaryV - 1) * rootedBoundaryReduced G r

/-- Claim 48270: the rooted and unrooted connected-subtree sums, their
singleton-root subtraction, and the rooted local current are polynomials in
Z[u,v] (represented as a nested polynomial ring). -/
def claim48270 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V),
    G.IsTree →
      rootedBoundaryPolynomial G r =
          boundaryV ^ boundaryDegree G r + rootedBoundaryNontrivial G r

section Grafting

variable {W : Type*} [Fintype W] [DecidableEq W]

def graftGraph (GX : SimpleGraph V) (GY : SimpleGraph W)
    (rx : V) (ry : W) : SimpleGraph (Sum V W) :=
  SimpleGraph.fromRel (fun x y =>
    match x, y with
    | Sum.inl x, Sum.inl x' => GX.Adj x x'
    | Sum.inr y, Sum.inr y' => GY.Adj y y'
    | Sum.inl x, Sum.inr y => x = rx ∧ y = ry
    | Sum.inr y, Sum.inl x => x = rx ∧ y = ry)

/-- Claim 48271: the one-edge grafting laws for the rooted and unrooted
boundary polynomials. -/
def claim48271 : Prop :=
  ∀ {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (GX : SimpleGraph V) (GY : SimpleGraph W) (rx : V) (ry : W),
    GX.IsTree →
      GY.IsTree →
        let Z := graftGraph GX GY rx ry
        rootedBoundaryPolynomial Z (Sum.inr ry) =
            rootedBoundaryPolynomial GY ry *
              (boundaryV + boundaryU * rootedBoundaryPolynomial GX rx) ∧
          unrootedBoundaryPolynomial Z =
            rootedBoundaryCurrent GX rx + rootedBoundaryCurrent GY ry +
              boundaryU * rootedBoundaryPolynomial GX rx *
                rootedBoundaryPolynomial GY ry

end Grafting

end BoundaryPolynomials

end

end MathlibPlus.Open.FormalizationBatch
