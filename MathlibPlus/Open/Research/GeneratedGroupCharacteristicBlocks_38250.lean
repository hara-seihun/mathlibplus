import MathlibPlus.Open.Research.GeneratedGroupExact

namespace MathlibPlus.Open.Research.GeneratedGroupExact

/-- Claim 38250: for every odd-prime eight-block mask pair, the two regular
    copies have the same characteristic fiber-orbit blocks and the pointwise
    equal induced terminal action. -/
def claim38250_characteristicBlocksAndTerminalImages : Prop :=
  ∀ q : ℕ, Nat.Prime q → 2 < q →
    ∀ μ : Mask,
      regularSubgroup (regularCopyR q) ∧
        regularSubgroup (regularCopyT q μ) ∧
        commonCharacteristicPartition q μ

end MathlibPlus.Open.Research.GeneratedGroupExact
