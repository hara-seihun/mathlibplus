import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2938ShiftedRepresentation

noncomputable section

/-- Claim 45283: the offset equation is exactly the distinct finite
representation equation after transporting the finite offset set to its
original indices. -/
def shiftedFiniteRepresentationEquivalence_claim45283 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ∀ D : Finset ℕ,
      (∀ d ∈ D, 0 < d) →
        let I : Finset ℕ := D.image (fun d => n + d)
        let offsetEquation : Prop :=
          (n : ℚ) =
            (∑ d ∈ D, ((n + d : ℕ) : ℚ) / (2 : ℚ) ^ d)
        let distinctRepresentation : Prop :=
          (∀ i ∈ I, n < i) ∧
            (n : ℚ) =
              (∑ i ∈ I, (i : ℚ) / (2 : ℚ) ^ (i - n))
        offsetEquation ↔ distinctRepresentation

end

end MathlibPlus.Open.ResearchFormalization.R2938ShiftedRepresentation
