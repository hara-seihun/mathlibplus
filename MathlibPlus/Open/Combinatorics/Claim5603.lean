import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim5603

/-- The finite root-jet carrier: degree, sibling-pair count, and root boundary load. -/
abbrev RootJet := ℕ × (ℕ × ℕ)

private def rootJetStar (x y : RootJet) : RootJet :=
  (x.1 + y.1, (x.2.1 + y.2.1 + x.1 * y.1, x.2.2 + y.2.2))

private def rootJetIdentity : RootJet :=
  (0, (0, 0))

private def branchJet (rootOutdegree : ℕ) : RootJet :=
  (1, (0, rootOutdegree))

private def rootJetFold (xs : List RootJet) : RootJet :=
  xs.foldl rootJetStar rootJetIdentity

private noncomputable def expandedRootJet {β : Type*} [DecidableEq β]
    (support : Finset β) (rootOutdegree : β → ℕ) (a : β → ℕ) : RootJet :=
  rootJetFold
    (support.toList.flatMap (fun β' =>
      List.replicate (a β') (branchJet (rootOutdegree β'))))

private def groupedFactor (rootOutdegree : ℕ) (a : ℕ) : RootJet :=
  (a, (Nat.choose a 2, a * rootOutdegree))

private noncomputable def groupedRootJet {β : Type*} [DecidableEq β]
    (support : Finset β) (rootOutdegree : β → ℕ) (a : β → ℕ) : RootJet :=
  rootJetFold
    (support.toList.map (fun β' =>
      groupedFactor (rootOutdegree β') (a β')))

/-- Binary parenthesizations of a fixed ordered list of root-jet factors. -/
inductive RootJetTree where
  | leaf (value : RootJet)
  | join (left right : RootJetTree)

private def RootJetTree.leaves : RootJetTree → List RootJet
  | .leaf value => [value]
  | .join left right => left.leaves ++ right.leaves

private def RootJetTree.evaluate : RootJetTree → RootJet
  | .leaf value => value
  | .join left right => rootJetStar left.evaluate right.evaluate

private def rootJetReassociationExact : Prop :=
  ∀ (left right : RootJetTree),
    left.leaves = right.leaves → left.evaluate = right.evaluate

/--
Claim 5603: distinct rooted branch types are grouped before taking the full
root jet.  Each type keeps its multiplicity and root outdegree, and the
associative star operation makes every binary reassociation exact.
-/
def groupedArbitraryArityFormula_claim5603 : Prop :=
  (∀ (x y z : RootJet),
    rootJetStar (rootJetStar x y) z = rootJetStar x (rootJetStar y z)) ∧
  (∀ (β : Type*) [DecidableEq β]
      (support : Finset β) (rootOutdegree : β → ℕ),
      ∀ (a : β → ℕ),
        expandedRootJet support rootOutdegree a =
          groupedRootJet support rootOutdegree a) ∧
  rootJetReassociationExact

end MathlibPlus.Open.Combinatorics.Claim5603
