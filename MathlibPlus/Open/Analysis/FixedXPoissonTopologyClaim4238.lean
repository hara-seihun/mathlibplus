import MathlibPlus.Analysis.SingleSpike
import MathlibPlus.Open.Analysis.LocalLipschitzTuranScalarClaim4232

open Filter
open scoped Topology

namespace MathlibPlus.Open.Analysis.FixedXPoissonTopologyClaim4238

noncomputable section

/-- The coefficient sequence of the exact single-spike family from Claim 4235,
viewed in the complex carrier used by the Poisson Turán form. -/
def spikeSequence (x : ℝ) (N : ℕ+) : ℕ → ℂ :=
  fun k =>
    (MathlibPlus.Analysis.SingleSpike.coefficient x (N : ℕ) k : ℂ)

/-- Claim 4238: at a fixed positive Poisson parameter, unshifted Fock
convergence does not control the Turán scalar in general, whereas convergence
in the first-shift graph norm does.  The continuity clause has no higher-shift
or higher-factorial-moment hypothesis. -/
def claim4238 : Prop :=
  (∀ x : ℝ, 0 < x →
    (∀ N : ℕ+,
      poissonM0_claim4227 x (spikeSequence x N) ^ 2 =
          1 / Real.sqrt (N : ℝ) ∧
        poissonM1_claim4227 x (spikeSequence x N) ^ 2 =
          Real.sqrt (N : ℝ) / x ∧
        MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
            x (spikeSequence x N) =
          (-(Real.sqrt (N : ℝ) / x) : ℝ)) ∧
      Filter.Tendsto
        (fun N : ℕ+ =>
          (poissonM0_claim4227 x (spikeSequence x N)) ^ 2)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (fun N : ℕ+ =>
          (poissonM1_claim4227 x (spikeSequence x N)) ^ 2)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun N : ℕ+ =>
          (MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
              x (spikeSequence x N)).re)
        Filter.atTop Filter.atBot) ∧
  (∀ (x : ℝ), 0 < x →
    ∀ (u : ℕ → ℂ) (s : ℕ → ℕ → ℂ),
      poissonGraphFinite_claim4227 x u →
      (∀ k : ℕ, poissonGraphFinite_claim4227 x (s k)) →
      Filter.Tendsto
          (fun k : ℕ => poissonGraphNorm_claim4227 x (s k - u))
          Filter.atTop (nhds (0 : ℝ)) →
      Filter.Tendsto
        (fun k : ℕ =>
          MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
            x (s k))
        Filter.atTop
        (nhds
          (MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
            x u)))

end

end MathlibPlus.Open.Analysis.FixedXPoissonTopologyClaim4238
