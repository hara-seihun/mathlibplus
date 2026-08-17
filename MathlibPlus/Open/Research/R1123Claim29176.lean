import MathlibPlus.Open.Research.R1123Claim29175

namespace MathlibPlus.Open.Research.R1123Claim29176

noncomputable section

open MathlibPlus.Open.Research

/-- Identity-free inverse-closed connection sets of the complementary
valency. -/
def highConnectionSet (S : Finset censusGroup) : Prop :=
  0 ∉ S ∧
    (∀ x : censusGroup, x ∈ S ↔ -x ∈ S) ∧
      S.card = 59

/-- Complementation inside the nonidentity elements of the fixed additive
census group. -/
def connectionComplement (S : Finset censusGroup) : Finset censusGroup :=
  (Finset.univ.erase (0 : censusGroup)) \ S

/-- Ordinary Cayley graph isomorphism for raw connection sets on the census
carrier. -/
def ordinaryGraphIso (S T : Finset censusGroup) : Prop :=
  ∃ e : censusGroup ≃ censusGroup, ∀ x y : censusGroup,
    (y - x ∈ S ↔ e y - e x ∈ T)

/-- Equivalence of raw connection sets under additive group automorphisms. -/
def additiveAutomorphismEquiv (S T : Finset censusGroup) : Prop :=
  ∃ e : censusGroup ≃+ censusGroup, ∀ x : censusGroup,
    (x ∈ S ↔ e x ∈ T)

/-- CI at valency fifty-nine, with the ordinary graph-isomorphism and
additive-automorphism relations written on the exact high-valency carrier. -/
def highValencyCI : Prop :=
  ∀ S T : Finset censusGroup,
    highConnectionSet S →
      highConnectionSet T →
        ordinaryGraphIso S T →
          additiveAutomorphismEquiv S T

/-- Claim 29176: inside the 71 nonidentity elements, complementation takes
exact valency-twelve connection sets to valency fifty-nine connection sets and
preserves both equivalence relations; the reviewed low-valency CI conclusion
therefore transfers to every high-valency graph. -/
def claim29176 : Prop :=
  claim_29175 →
    Fintype.card censusGroup = 72 ∧
      (Finset.univ.erase (0 : censusGroup)).card = 71 ∧
        (∀ S : connectionSet censusGroup,
          (connectionComplement S.1).card = 71 - S.1.card ∧
            (connectionComplement S.1).card = 59 ∧
              highConnectionSet (connectionComplement S.1)) ∧
          (∀ S T : connectionSet censusGroup,
            ordinaryGraphIso S.1 T.1 ↔
              ordinaryGraphIso (connectionComplement S.1)
                (connectionComplement T.1)) ∧
            (∀ S T : connectionSet censusGroup,
              additiveAutomorphismEquiv S.1 T.1 ↔
                additiveAutomorphismEquiv (connectionComplement S.1)
                  (connectionComplement T.1)) ∧
              highValencyCI

end

end MathlibPlus.Open.Research.R1123Claim29176
