import MathlibPlus.Open.ResearchFormalization.R3390BicentroidClaim50115

namespace MathlibPlus.Open.ResearchFormalization.R3390

open scoped BigOperators

noncomputable section

/-- The polynomial contribution in which the two one-core sectors are formed
without selecting the central edge. -/
def centralEdgeAbsentSector (A B : RootedTree) : ComponentPolynomial :=
  componentSelector
      ((Polynomial.X : BoundaryPolynomial) *
        rootedFactorProduct (RootedTree.children A)) *
    componentSelector
      ((Polynomial.X : BoundaryPolynomial) *
        rootedFactorProduct (RootedTree.children B))

/-- The sector selected by the central edge: the open-size two equator is
closed by `componentSelector`. -/
def selectedCentralEdgeBalancedEquatorSector
    (A B : RootedTree) : ComponentPolynomial :=
  componentSelector
    ((Polynomial.X : BoundaryPolynomial) ^ 2 *
      rootedFactorProduct (RootedTree.children A) *
      rootedFactorProduct (RootedTree.children B))

/-- Every variable occurring in a component-polynomial monomial records a
component order. -/
def componentOrdersAtMost (h : ℕ) (Q : ComponentPolynomial) : Prop :=
  ∀ m ∈ Q.support, ∀ n ∈ m.support, n ≤ h

/-- R-3390 Claim 50107: the ordinary bicentroid polynomial has precisely its
central-edge-absent one-core sector and its selected balanced-equator sector;
the former contains no component larger than either order-`h` half. -/
def claim50107 : Prop :=
  ∀ (h : ℕ) (A B : RootedTree),
    let T := biNode A B
    isBicentroidParent h T →
      RootedTree.order A + RootedTree.order B = 2 * h ∧
        parentUPolynomial T =
          centralEdgeAbsentSector A B +
            selectedCentralEdgeBalancedEquatorSector A B ∧
        componentOrdersAtMost h (centralEdgeAbsentSector A B)

end
end MathlibPlus.Open.ResearchFormalization.R3390
