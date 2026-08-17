import MathlibPlus.Open.Research.R4031Claim51988

namespace MathlibPlus.Open.ResearchFormalization.R4031Claim51957

open scoped BigOperators
open MathlibPlus.Open.Research.R4031Claim51988

noncomputable section

abbrev BooleanLaw (n : ℕ) := Atom n → ℝ

def isProbabilityLaw {n : ℕ} (mu : BooleanLaw n) : Prop :=
  (∀ k, 0 ≤ mu k) ∧
    (∑ k : Atom n, mu k) = 1

noncomputable def lawExpectation {n : ℕ} (mu : BooleanLaw n)
    (f : Atom n → ℝ) : ℝ :=
  ∑ k : Atom n, mu k * f k

noncomputable def lawBarycentre {n : ℕ} (mu : BooleanLaw n) : Table n :=
  fun x => ∑ k : Atom n, mu k * atomValue k x

/-- The q-optimal constrained loss is within the driver query cost of the
unrestricted loss, and the corresponding finite-law average obeys the stated
bound. -/
def claim51957 : Prop :=
  ∀ (n : ℕ) (mu : BooleanLaw n) (k : Atom n),
    isProbabilityLaw mu →
      let v := lawBarycentre mu
      constrainedLoss k v - unrestrictedLoss v ≤ queryCost k ∧
        lawExpectation mu (fun j => constrainedLoss j v) - unrestrictedLoss v ≤
          lawExpectation mu queryCost

end
end MathlibPlus.Open.ResearchFormalization.R4031Claim51957
