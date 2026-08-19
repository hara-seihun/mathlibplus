import MathlibPlus.Open.ResearchFormalization.R1404CarryAtlas

namespace MathlibPlus.Open.ResearchFormalization.R1404.Claim38680

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1404

/-- The order of the generated directed binary two-closure attached to a miss
row. -/
def closureOrder (r : atlasFailureRows) : ℕ :=
  Nat.card
    {h : AtlasPermutation //
      h ∈ directedBinaryTwoClosure (generatedPair r.1.1 r.1.2)}

/-- Claim 38680: the five closure-order bins exhaust the 572 defining-
transporter miss rows with the asserted multiplicities. -/
def claim38680_exactClosureOrderHistogram : Prop :=
  Nat.card atlasFailureRows = 572 ∧
    Nat.card {r : atlasFailureRows // closureOrder r = 27} = 8 ∧
    Nat.card {r : atlasFailureRows // closureOrder r = 243} = 72 ∧
    Nat.card {r : atlasFailureRows // closureOrder r = 1944} = 24 ∧
    Nat.card {r : atlasFailureRows // closureOrder r = 17496} = 36 ∧
    Nat.card {r : atlasFailureRows // closureOrder r = 1088640} = 432 ∧
    (∀ r : atlasFailureRows,
      closureOrder r = 27 ∨
      closureOrder r = 243 ∨
      closureOrder r = 1944 ∨
      closureOrder r = 17496 ∨
      closureOrder r = 1088640) ∧
    8 + 72 + 24 + 36 + 432 = 572

end

end MathlibPlus.Open.ResearchFormalization.R1404.Claim38680
