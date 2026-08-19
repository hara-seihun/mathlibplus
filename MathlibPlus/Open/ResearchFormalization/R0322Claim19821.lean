import MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19821

open scoped BigOperators Classical
open MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

noncomputable section

private def connectedSubsetCarrier {A B : LegFamily} (c : ℕ) :
    Finset (Finset (DoubleSpiderVertex A B c)) :=
  (Finset.univ : Finset (Finset (DoubleSpiderVertex A B c))).filter
    (fun S => S.Nonempty ∧
      ((doubleSpiderGraph A B c).induce (S : Set _)).Connected)

private def boundaryPolynomialExpansion {A B : LegFamily} (c : ℕ) :
    BoundaryPoly :=
  ∑ S ∈ connectedSubsetCarrier c,
    uBoundaryVar ^ S.card *
      vBoundaryVar ^
        (boundaryEdgeSet (doubleSpiderGraph A B c) S).card

private def branchPathAdjacency {A B : LegFamily} (c : ℕ) : Prop :=
  let G := doubleSpiderGraph A B c
  (∀ r s : Fin (c + 1),
    G.Adj (Sum.inl r) (Sum.inl s) ↔
      r ≠ s ∧ (r.val + 1 = s.val ∨ s.val + 1 = r.val)) ∧
    (∀ (r : Fin (c + 1)) (x : LegVertex A),
      G.Adj (Sum.inl r) (Sum.inr (Sum.inl x)) ↔
        r.val = 0 ∧ x.2.val = 0) ∧
      (∀ (r : Fin (c + 1)) (y : LegVertex B),
        G.Adj (Sum.inl r) (Sum.inr (Sum.inr y)) ↔
          r.val = c ∧ y.2.val = 0) ∧
        (∀ (x y : LegVertex A),
          G.Adj (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inl y)) ↔
            legAdjacent x y) ∧
          (∀ (x y : LegVertex B),
            G.Adj (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inr y)) ↔
              legAdjacent x y) ∧
            (∀ (x : LegVertex A) (y : LegVertex B),
              ¬ G.Adj (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inr y)))

def boundaryRefinedConnectedSubtreePolynomial_claim19821 : Prop :=
  ∀ (A B : LegFamily) (c : ℕ),
    admissibleDoubleSpider A B c →
      1 ≤ c ∧
        2 ≤ A.count ∧
          2 ≤ B.count ∧
            positiveLegFamily A ∧
              positiveLegFamily B ∧
                branchPathAdjacency (A := A) (B := B) c ∧
                  (∀ (S : Finset (DoubleSpiderVertex A B c))
                    (e : Sym2 (DoubleSpiderVertex A B c)),
                    e ∈ boundaryEdgeSet (doubleSpiderGraph A B c) S ↔
                      ∃ u v, e = s(u, v) ∧
                        ((u ∈ S ∧ v ∉ S) ∨
                          (u ∉ S ∧ v ∈ S)) ∧
                            (doubleSpiderGraph A B c).Adj u v) ∧
                    boundaryPolynomial (doubleSpiderGraph A B c) =
                      boundaryPolynomialExpansion (A := A) (B := B) c

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19821
