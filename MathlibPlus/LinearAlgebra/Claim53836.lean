import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 53836 (R-4992#S5): in the one-cell rational system with
`L(e) = 1`, the nonnegative image does not contain the signed target `-1`.
The image is written as the range of scalar multiplication by the one-cell
basis value `1`. -/
theorem nonnegativeOneCellImage_excludesNegOne_claim53836 :
    ¬ ((-1 : ℚ) ∈ Set.range (fun c : {q : ℚ // 0 ≤ q} => (c : ℚ) * 1)) := by
  rintro ⟨c, hc⟩
  have hnonneg : (0 : ℚ) ≤ c := c.property
  norm_num at hc
  linarith

end MathlibPlus.LinearAlgebra
