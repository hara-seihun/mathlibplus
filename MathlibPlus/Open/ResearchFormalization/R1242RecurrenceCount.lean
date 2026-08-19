import MathlibPlus.Open.FormalizationBatch.R1242Claim30519

namespace MathlibPlus.Open.ResearchFormalization.R1242RecurrenceCount

noncomputable section

open MathlibPlus.Open.FormalizationBatch.R1242Claim30519

/-- Claim 30518: for every admitted nonzero direction/profile and every fixed
`t`, the exact normalized recurrence carrier is a six-dimensional affine
space with `3^(3+3)=729` tables. -/
def fixedRecurrenceTableCount_claim30518 : Prop :=
  ∀ (x : Plane),
    x ≠ 0 → ell x ≠ 0 →
      ∀ (H : Plane → F3),
        H ≠ 0 →
          (∀ s : Plane, H (s + x) = H s) →
            ∀ t : F3,
              Nat.card {F : Table // F ∈ recurrenceSet x H t} =
                3 ^ (3 + 3) ∧
                Nat.card {F : Table // F ∈ recurrenceSet x H t} = 729

end

end MathlibPlus.Open.ResearchFormalization.R1242RecurrenceCount
