import MathlibPlus.Open.ResearchFormalizationBatch_01a001b3_443b_7727_a88a_7b55e0d6fe72.Linear

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.D0084Claim5158

open MathlibPlus.Open.ResearchFormalizationBatch_01a001b3_443b_7727_a88a_7b55e0d6fe72

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def radiusWidthBlockArity_claim5158
    {F R V B : Type} [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] [DecidableEq V]
    (M : Matrix R V F) (block : R → B) (S₀ S : Finset V)
    (r : ℕ) (v : {w : V // w ∈ S}) : WithTop ℕ :=
  let hasArity : ℕ → Prop := fun k =>
    ∃ J : Finset B,
      J.card = k ∧
        J ⊆ radiusBlocks M block S₀ v.1 r ∧
          ∃ coeff : rowOver block J → F,
            ∀ s : {w : V // w ∈ S},
              (∑ q : rowOver block J, coeff q * M q.1 s.1) =
                if s.1 = v.1 then 1 else 0
  if h : ∃ k : ℕ, hasArity k then
    (Nat.find h : WithTop ℕ)
  else
    ⊤

end
end MathlibPlus.Open.ResearchFormalization.D0084Claim5158
