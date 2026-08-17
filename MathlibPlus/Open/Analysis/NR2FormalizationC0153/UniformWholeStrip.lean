import Mathlib
import MathlibPlus.Open.Analysis.AdmittedGaussianBatch

open Filter MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.NR2FormalizationC0153

noncomputable section

/-- Claim 2420: the explicit logarithmic endpoint-flat arithmetic transform
converges uniformly on every closed horizontal strip to the centered Xi
function with the `1/(2π)` normalization. -/
def uniformWholeStripXiConvergence_claim2420 : Prop :=
  let h : ℝ → ℝ := fun x =>
    x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)
  let g0 : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let xi : ℂ → ℂ := fun s =>
    s * (s - 1) / 2 * completedRiemannZeta s
  let Xi : ℂ → ℂ := fun z =>
    xi ((1 / 2 : ℂ) + Complex.I * z)
  ∀ Y : ℝ, 0 ≤ Y → Y < 1 / 2 →
    ∃ CY : ℝ, 0 ≤ CY ∧
      ∀ᶠ lam : ℝ in atTop,
        1 < lam →
          let r : ℕ := ⌊Real.log lam⌋₊
          let m : ℕ := 2 * r + 2
          let wlam : ℝ → ℝ := fun x =>
            if |x| ≤ lam then (1 - x ^ 2 / lam ^ 2) ^ m else 0
          let blam : ℝ :=
            (∫ x in (-lam : ℝ)..lam, wlam x * h x) /
              (∫ x in (-lam : ℝ)..lam, wlam x * g0 x)
          let qlam : ℝ → ℝ := fun x =>
            if |x| ≤ lam then wlam x * (h x - blam * g0 x) else 0
          let klam : ℝ → ℝ := fun y =>
            Real.exp (y / 2) *
              ∑' n : ℕ,
                if 1 ≤ n then qlam ((n : ℝ) * Real.exp y) else 0
          let Flam : ℂ → ℂ := fun z =>
            ∫ y in (-Real.log lam : ℝ)..Real.log lam,
              (klam y : ℂ) * Complex.cos (z * (y : ℂ))
          sSup {v : ℝ | ∃ z : ℂ,
            |z.im| ≤ Y ∧
            v = ‖Flam z - Xi z / (2 * (Real.pi : ℂ))‖} ≤
            CY * Real.log lam * Real.rpow lam (-3 / 2 + Y)

end
end MathlibPlus.Open.Analysis.NR2FormalizationC0153
