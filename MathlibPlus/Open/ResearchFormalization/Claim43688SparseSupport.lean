import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim43688

/-- The sparse representative vertex count and the equivalent host-order
support inequality. -/
def sparseAttachmentSupportIdentity_claim43688 : Prop :=
  ∀ (v a d n : ℕ),
    a ≤ d →
    d + 1 ≤ n →
    a ≤ v →
      let representativeVertices := v + 1 + d - a
      representativeVertices = v + 1 + d - a ∧
        (representativeVertices ≤ n ↔
          v - a ≤ n - 1 - d)

end MathlibPlus.Open.ResearchFormalization.Claim43688
