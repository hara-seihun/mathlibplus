import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim4935

/-- Folding an even pair over the two Boolean signs gives the two evaluations at
`c + z` and `c - z`. -/
theorem foldedEntry_evenPair_sum {ι α β : Type*} [AddGroup α] [AddCommMonoid β]
    (K : ι → α → β) (i : ι) (c z : α) :
    (∑ b : Bool, K i (c + if b then z else -z)) =
      K i (c + z) + K i (c - z) := by
  simp [sub_eq_add_neg]

end MathlibPlus.Algebra.Claim4935
