import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.C0145

def endpointPartialZetaSine_claim2282 (c : ℕ) (r z : ℝ) : ℝ :=
  let L := Real.log c
  r * Real.sin (L * z / 2) +
    ∑ n ∈ (Finset.range c).filter (fun n => 1 ≤ n),
      (1 / Real.sqrt (n : ℝ)) * Real.sin (z * (L / 2 - Real.log n))

end MathlibPlus.Open.ResearchBatch.C0145
