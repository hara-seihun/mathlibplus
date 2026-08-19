import MathlibPlus.Open.Analysis.BooleanOrientationCharacterDeterminantExpansion7440

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.K0011Claim7448

open MathlibPlus.Open.Analysis

noncomputable section

/-- The negative Boolean chamber cut out by the admitted orientation character. -/
abbrev NegativeChamber7448 (r : ℕ) :=
  {ε : Fin r → Bool // booleanOrientationCharacter r ε < 0}

/-- The positive Boolean chamber cut out by the admitted orientation character. -/
abbrev PositiveChamber7448 (r : ℕ) :=
  {ε : Fin r → Bool // 0 < booleanOrientationCharacter r ε}

/-- A packet-dependent type-B transport has nonnegative entries and unit rows
on exactly the negative and positive character chambers. -/
def typeBReflectionTransport_claim7448
    (r : ℕ) (q l : Fin r → ℝ)
    (T : Matrix (NegativeChamber7448 r) (PositiveChamber7448 r) ℝ) : Prop :=
  (∀ i, 0 < q i) ∧
    StrictMono q ∧
    (∀ j, 1 < l j) ∧
    StrictMono l ∧
    (∀ ε : NegativeChamber7448 r,
      ∀ δ : PositiveChamber7448 r, 0 ≤ T ε δ) ∧
    (∀ ε : NegativeChamber7448 r,
      ∑ δ : PositiveChamber7448 r, T ε δ = 1)

end

end MathlibPlus.Open.Analysis.K0011Claim7448
