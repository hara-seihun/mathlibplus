import MathlibPlus.Open.Research.GeneratedGroupExact

namespace MathlibPlus.Open.Research.FormalizationBatch.R1363Claim38253

open MathlibPlus.Open.Research.GeneratedGroupExact

/-- Claim 38253: every conjugator in the generated group carrying the regular
copy `R` to `T_μ` forces the mask, up to a constant sign, into the generated
cyclic sign code; the bridge includes the block-fixing reduction for a
block-moving conjugator. -/
def claim38253 : Prop :=
  ∀ q : ℕ, ∀ hq : Nat.Prime q, 2 < q →
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ μ : Mask, conjugacySignBridge q μ

end MathlibPlus.Open.Research.FormalizationBatch.R1363Claim38253
