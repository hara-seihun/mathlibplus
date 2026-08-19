import MathlibPlus.Open.Research.R3193.Claim47053

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R3193.Claim47051

open MathlibPlus.Open.Research.R3193

private noncomputable def posteriorMeanFormula (n : ℕ) (j : Fin n)
    (ω : RademacherSample n) : ℝ :=
  if ω.u j = true ∧ ω.v j = true then
    ((1 + (n - 1 : ℝ) * p) / (n : ℝ)) * rademacherValue ω.a
  else
    rademacherValue (ω.b j) / (n : ℝ)

/-- The exact common/private posterior-mean branches and the resulting
posterior-variance decrement for the retained shared-bit Rademacher model. -/
def claim47051 : Prop :=
  ∀ (n : ℕ) (j : Fin n),
    (∀ ω : RademacherSample n,
      conditionalAverage (componentTranscript n j)
          (fun ω' => mu n ω') ω = posteriorMeanFormula n j ω) ∧
    deltaV n j =
      (p * (1 + (n - 1 : ℝ) * p) ^ 2 + 1 - p) / (n : ℝ) ^ 2

end MathlibPlus.Open.ResearchFormalization.R3193.Claim47051
