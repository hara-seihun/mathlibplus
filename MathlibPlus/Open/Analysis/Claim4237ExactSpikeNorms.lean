import Mathlib
import MathlibPlus.Open.Analysis.PolarizedTuranClaim4225
import MathlibPlus.Open.Analysis.SingleSpikeDisappearance

open Filter
open scoped Topology

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim4237

noncomputable def spikeSequence4237 (x : ℝ) (N : ℕ+) (n : ℕ) : ℂ :=
  if n = (N : ℕ) then
    (MathlibPlus.Open.Analysis.spikeHeight x N : ℂ)
  else 0

noncomputable def mZero4237 (x : ℝ) (u : ℕ → ℂ) : ℝ :=
  Real.sqrt
    (∑' n : ℕ,
      MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.poissonWeight x n *
        Complex.normSq (u n))

noncomputable def mOne4237 (x : ℝ) (u : ℕ → ℂ) : ℝ :=
  Real.sqrt
    (∑' n : ℕ,
      MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.poissonWeight x n *
        Complex.normSq (u (n + 1)))

noncomputable def turanScalar4237 (x : ℝ) (u : ℕ → ℂ) : ℂ :=
  MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar x u

def exactSpikeNormsAndDivergentTuran_claim4237 : Prop :=
  ∀ x : ℝ, 0 < x →
    (∀ N : ℕ+,
      (mZero4237 x (spikeSequence4237 x N)) ^ 2 =
        Real.rpow (N : ℝ) (-(1 / 2 : ℝ))) ∧
    (∀ N : ℕ+,
      (mOne4237 x (spikeSequence4237 x N)) ^ 2 =
        Real.sqrt (N : ℝ) / x) ∧
    (∀ N : ℕ+,
      turanScalar4237 x (spikeSequence4237 x N) =
        ((-(Real.sqrt (N : ℝ) / x) : ℝ) : ℂ)) ∧
    Filter.Tendsto
      (fun N : ℕ+ => (mZero4237 x (spikeSequence4237 x N)) ^ 2)
      Filter.atTop (nhds (0 : ℝ)) ∧
    Filter.Tendsto
      (fun N : ℕ+ => (mOne4237 x (spikeSequence4237 x N)) ^ 2)
      Filter.atTop Filter.atTop ∧
    Filter.Tendsto
      (fun N : ℕ+ =>
        (turanScalar4237 x (spikeSequence4237 x N)).re)
      Filter.atTop Filter.atBot

end MathlibPlus.Open.Analysis.Claim4237

end
