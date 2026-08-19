import Mathlib

namespace MathlibPlus.Open.Analysis.Claim13461

/-- The even and odd coordinates of a componentwise product of two real-type
reflection doublets. -/
def componentwiseProductCoordinates : Prop :=
  ∀ (dEven dOdd zEven zOdd : ℝ),
    let dPlus : ℂ := (dEven : ℂ) + Complex.I * (dOdd : ℂ)
    let zPlus : ℂ := (zEven : ℂ) + Complex.I * (zOdd : ℂ)
    let yPlus : ℂ := dPlus * zPlus
    yPlus.re = dEven * zEven - dOdd * zOdd ∧
      yPlus.im = dEven * zOdd + dOdd * zEven

end MathlibPlus.Open.Analysis.Claim13461
