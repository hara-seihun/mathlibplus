import Mathlib

namespace MathlibPlus.Analysis.Claim15663

/-- Claim 15663: the displayed profile rate is the peak term minus the entropy loss.
The source does not specify the ambient domain; this algebraic identity is stated
for arbitrary real `r`, `q`, and `d`. -/
theorem profileRate_eq_peak_sub_entropy (r q d : ℝ) :
    2 * r + q * (1 + Real.log (d / q)) =
      (d + 2 * r) - (d - q - q * Real.log (d / q)) := by
  ring

end MathlibPlus.Analysis.Claim15663
