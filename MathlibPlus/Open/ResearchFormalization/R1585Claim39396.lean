import MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension

noncomputable section

/-- Two rooted presentations of one unrooted host which are not rooted-isomorphic. -/
def nonisomorphicRootings39396 (R S : RootedTree) : Prop :=
  sameUnrootedHost R S ∧ ¬ sameRootedHost R S

/-- The general cross-root suspension theorem on the rooted-child-list carrier. -/
def claim39396_generalCrossRootSuspension : Prop :=
  ∀ (R S : RootedTree) (context : List RootedTree)
    (U : UPolynomial) (r d : ℕ),
    nonisomorphicRootings39396 R S →
    U = rootedU R →
    U = rootedU S →
    context.foldr (fun tree total => RootedTree.order tree + total) 0 =
      2 * r + 2 →
    2 * r + 2 ≤ RootedTree.order R →
    2 * r + 2 ≤ d →
    let a := RootedTree.order R
    let D := pruningFactor R - pruningFactor S
    let K := rootDeletionDifference R S
    hasExactFirstRow d D →
    D.coeff (a - 1) = K →
    K ≠ 0 →
    let h := a + r + 1
    let Tminus := centroidTreeMinus context R S
    let Tplus := centroidTreePlus context R S
    RootedTree.order Tminus = 2 * a + 2 * r + 2 ∧
      RootedTree.order Tplus = 2 * a + 2 * r + 2 ∧
      MathlibPlus.Open.Combinatorics.DTreeUPolynomial.unicentroidal
        (underlyingGraph Tminus) ∧
      MathlibPlus.Open.Combinatorics.DTreeUPolynomial.unicentroidal
        (underlyingGraph Tplus) ∧
      ¬ sameUnrootedHost Tminus Tplus ∧
      (∀ j, h ≤ j → j ≤ h + r →
        pureComponentPolynomial ((productHalfMinus context R S).coeff j) ∧
          pureComponentPolynomial ((productHalfPlus context R S).coeff j) ∧
          (productHalfMinus context R S).coeff j =
            (productHalfPlus context R S).coeff j) ∧
      centroidCardDifference context R S ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension
