import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The normalization of the single-spike exponential generating function. -/
def spikeHeight (x : ℝ) (N : ℕ+) : ℝ :=
  Real.exp (x / 2) *
    Real.sqrt (Nat.factorial (N : ℕ) : ℝ) *
    Real.rpow x (-((N : ℝ) / 2)) *
    Real.rpow (N : ℝ) (-(1 / 4 : ℝ))

/-- The single-spike polynomial with its only coefficient at index `N`. -/
def spikePolynomial (x : ℝ) (N : ℕ+) (z : ℂ) : ℂ :=
  (spikeHeight x N : ℂ) * z ^ (N : ℕ) /
    (Nat.factorial (N : ℕ) : ℂ)

/-- The value asserted for the supremum on a disk in the single-spike family. -/
def spikeSupFormula (x R : ℝ) (N : ℕ+) : ℝ :=
  Real.exp (x / 2) *
    Real.rpow (N : ℝ) (-(1 / 4 : ℝ)) *
    (R / Real.sqrt x) ^ (N : ℕ) /
    Real.sqrt (Nat.factorial (N : ℕ) : ℝ)

/-- Compact-open disappearance of the single-spike exponential generating function. -/
def compactOpenDisappearanceOfSpikeEGF : Prop :=
  ∀ (x R : ℝ), 0 < x → 0 ≤ R →
    ( (∀ N : ℕ+,
        sSup ((fun z : ℂ => ‖spikePolynomial x N z‖) ''
          {z : ℂ | ‖z‖ ≤ R}) = spikeSupFormula x R N) ∧
      Filter.Tendsto (fun N : ℕ+ => spikeSupFormula x R N)
        Filter.atTop (nhds (0 : ℝ)) )

end MathlibPlus.Open.Analysis
