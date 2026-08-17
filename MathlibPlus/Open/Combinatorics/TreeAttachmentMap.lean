import MathlibPlus.Open.Combinatorics.TreeAttachment

namespace MathlibPlus.Open.Combinatorics.TreeAttachment

noncomputable section

/-- The leaf-attachment map `A_n` on rooted `(n - 1)`-tree cards. -/
noncomputable def leafAttachmentMap_claim5133 (n : ℕ) (h : 1 ≤ n) :
    RootedCardSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  attachmentLinearizationAt n h

end
end MathlibPlus.Open.Combinatorics.TreeAttachment
