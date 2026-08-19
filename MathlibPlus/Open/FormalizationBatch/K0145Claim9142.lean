import MathlibPlus.Open.FormalizationBatchK0145

namespace MathlibPlus.Open.FormalizationBatch.K0145Claim9142

open MathlibPlus.Open.FormalizationBatchK0145

noncomputable section

/-- The group orders listed by the admitted order distribution. -/
def automorphismOrders9142 : Finset ℕ :=
  {1, 2, 3, 4, 6, 8, 12, 16, 24, 36, 48}

/-- Claim 9142: the complete `R(4,5)` catalogue has the stated
automorphism-group-order distribution and no other order. -/
def exactAutomorphismGroupOrderDistribution_claim9142 : Prop :=
  Fintype.card {c : GraphClass24 // ClassHasR45 c} = 352366 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 1} = 341171 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 2} = 10566 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 3} = 35 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 4} = 508 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 6} = 19 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 8} = 49 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 12} = 8 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 16} = 3 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 24} = 3 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 36} = 1 ∧
    Fintype.card {c : GraphClass24 // ClassHasAutCard c 48} = 3 ∧
    (∀ n : ℕ, n ∉ automorphismOrders9142 →
      Fintype.card {c : GraphClass24 // ClassHasAutCard c n} = 0)

end

end MathlibPlus.Open.FormalizationBatch.K0145Claim9142
