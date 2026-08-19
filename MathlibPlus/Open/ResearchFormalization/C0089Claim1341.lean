import MathlibPlus.Open.ResearchFormalization.C0089Claim1337

namespace MathlibPlus.Open.ResearchFormalization.C0089Claim1341

noncomputable section

open MathlibPlus.Open.ResearchFormalization.C0089
open MathlibPlus.Open.ResearchFormalization.C0089Claim1337

/-- The exact half-open interval containing the final crossing for coefficient
`1.149`. -/
def finalCrossingInterval1341 : Prop :=
  ∃ x : ℝ,
    (42575222504 : ℝ) < x ∧
      x < (42575222505 : ℝ) ∧
      B x = (1.149 : ℝ) ∧
      (42575222504.983670614181 : ℝ) ≤ x ∧
      x < (42575222504.983670614182 : ℝ)

/-- Claim 1341: the exact least start and unique final crossing for coefficient
`1.149`, with the source's trailing-decimal interval semantics. -/
def claim_1341 : Prop :=
  leastIntegerStart (1.149 : ℝ) 42575222505 ∧
    finalRealEquality (1.149 : ℝ) 42575222505 ∧
    finalCrossingInterval1341

end

end MathlibPlus.Open.ResearchFormalization.C0089Claim1341
