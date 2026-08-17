import MathlibPlus.Open.Analysis.BesselKernelBounds
import MathlibPlus.Open.Analysis.PositiveAxisPoissonBessel
import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb03937c429c8f533ab1b48622

namespace MathlibPlus.Open.Analysis.Claim10110

open MathlibPlus.Analysis.BesselK
open MathlibPlus.Open.ResearchFormalizationBatch01
open MathlibPlus.Open.Analysis.PositiveAxisPoissonBessel

noncomputable section

/-- The weighted von Mangoldt discrepancy `B(t)` in the admitted formula. -/
def discrepancyB (t : ℝ) : ℝ :=
  weightedVonMangoldtSum t - t + eulerGamma

/-- The order-two Bessel kernel in the admitted integral. -/
def j2Kernel (x t : ℝ) : ℝ :=
  besselJ 2 (2 * Real.sqrt (x * t)) / t

/-- The absolutely convergent J2 representation of the finite-place Poisson sum. -/
def claim10110 : Prop :=
  ∀ x : ℝ, 0 < x →
    (Real.exp (-x) *
        (∑' n : ℕ,
          if 1 ≤ n then
            finitePlaceLiMoment n * x ^ n / (Nat.factorial n : ℝ)
          else 0) =
      -eulerGamma * x +
        x * (∫ t in Set.Ioi (0 : ℝ), j2Kernel x t * discrepancyB t)) ∧
    MeasureTheory.IntegrableOn
      (fun t : ℝ => j2Kernel x t * discrepancyB t)
      (Set.Ioi (0 : ℝ))

end

end MathlibPlus.Open.Analysis.Claim10110
