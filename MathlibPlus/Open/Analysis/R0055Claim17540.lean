import Mathlib

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.R0055Claim17540

noncomputable section

/-- The finite-prime jump measure whose atoms are the jumps of the
scattering process. -/
def scatteringJumpMeasure (P : Finset ℕ) : Measure ℝ :=
  ∑ p ∈ P, Measure.sum (fun r : {r : ℕ // 0 < r} =>
    (ENNReal.ofReal
        (Real.rpow (p : ℝ) (-((r.1 : ℝ) / 2)) / (r.1 : ℝ))) •
      Measure.dirac ((r.1 : ℝ) * Real.log (p : ℝ)))

/-- The m-th scattering cumulant is the m-th moment of the jump measure. -/
def scatteringCumulant (P : Finset ℕ) (m : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ m ∂ scatteringJumpMeasure P

/-- Claim 17540: the odd scattering cumulant is the displayed prime series,
with its cumulant carrier fixed by the corresponding jump measure. -/
def claim17540_primeSeriesFormula : Prop :=
  ∀ (P : Finset ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    P.Nonempty →
    ∀ m : ℕ, Odd m →
      scatteringCumulant P m =
        ∑' p : {p // p ∈ P},
          ∑' r : ℕ+,
            (r : ℝ) ^ (m - 1) *
                (Real.log (p.1 : ℝ)) ^ m *
              Real.rpow (p.1 : ℝ) (-((r : ℝ) / 2))

end

end MathlibPlus.Open.Analysis.R0055Claim17540
