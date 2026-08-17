import Mathlib

namespace MathlibPlus.Open.Analysis.Claim52257

/-- Claim 52257: every parameter on the target curve has a right-region
zero in the displayed collision window for the exact quartic carrier. -/
def uniformTargetCurveCollisionWitness : Prop :=
  let L : ℝ := (1529 : ℝ) / 10000
  let _T : ℝ := (3377 : ℝ) / 20000
  let τ : ℝ := (1287 : ℝ) / 8000
  let X : ℝ := 6000000185827
  let c : ℝ := X + 2
  let F : ℝ → ℂ → ℂ := fun t z =>
    let s : ℝ := τ - t
    z ^ 4 +
        ((12 * s - 2 * c ^ 2 : ℝ) : ℂ) * z ^ 2 +
        ((c ^ 4 - 4 * c ^ 2 * s + 12 * s ^ 2 : ℝ) : ℂ)
  ∀ q : ℝ, q ∈ Set.Icc (0 : ℝ) (2 * L) →
    let t_q : ℝ := L - q / 2
    let y : ℝ := Real.sqrt q
    ∃ u v : ℝ,
      F t_q ((u : ℂ) + (v : ℂ) * Complex.I) = 0 ∧
        u > X + Real.sqrt (1 - q) ∧
        y < v ∧
        v < Real.sqrt (1 - 2 * t_q)

end MathlibPlus.Open.Analysis.Claim52257
