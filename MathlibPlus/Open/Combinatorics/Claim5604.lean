import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.Claim5604

/-- The fixed three-register interface used by the root-jet formulas. -/
abbrev RootJet := ℕ × (ℕ × ℕ)

/-- The four attachment channels at a vertex. -/
abbrev AttachmentChannels := ℕ × (ℕ × (ℕ × ℕ))

private def rootJetStar (x y : RootJet) : RootJet :=
  (x.1 + y.1, (x.2.1 + y.2.1 + x.1 * y.1, x.2.2 + y.2.2))

private def rootJetIdentity : RootJet :=
  (0, (0, 0))

private def repeatedBranchJet (a d : ℕ) : RootJet :=
  List.foldl rootJetStar rootJetIdentity (List.replicate a (1, (0, d)))

private def groupedRootJet (groups : List (ℕ × ℕ)) : RootJet :=
  List.foldl rootJetStar rootJetIdentity
    (groups.map (fun p => (p.1, (Nat.choose p.1 2, p.1 * p.2))))

private def attachmentChannels
    (m : ℕ) (rootLoads : Fin m → ℕ) : AttachmentChannels :=
  (1, (m, (Nat.choose m 2, Finset.univ.sum rootLoads)))

/--
Claim 5604: arbitrary degree and sibling multiplicity affect only the values
in one fixed RootJet triple and the four fixed attachment channels.
-/
def fixedSizeInterface : Prop :=
  (∀ (a d : ℕ),
    repeatedBranchJet a d = (a, (Nat.choose a 2, a * d))) ∧
  (∀ (groups : List (ℕ × ℕ)),
    groupedRootJet groups =
      ((groups.map (fun p => p.1)).sum,
        ((groups.map (fun p => Nat.choose p.1 2)).sum,
          (groups.map (fun p => p.1 * p.2)).sum))) ∧
  (∀ (m : ℕ) (rootLoads : Fin m → ℕ),
    attachmentChannels m rootLoads =
      (1, (m, (Nat.choose m 2, Finset.univ.sum rootLoads))))

end MathlibPlus.Open.Combinatorics.Claim5604
