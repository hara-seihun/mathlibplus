import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0338.PositiveOrderAndDeltaPrime15523_15526

open scoped BigOperators Distributions Topology
open Set TopologicalSpace Distribution

namespace MathlibPlus.Open.ResearchFormalization.O0338

noncomputable section

/-- The order-zero distribution carried by a point mass at `x`. -/
noncomputable def localDeltaMass (x : ℝ) : RealDistribution :=
  Distribution.delta (Ω := (⊤ : TopologicalSpace.Opens ℝ))
    (n := ⊤) x

/-- Restriction to the lower-edge neighborhood, represented on every test
function supported below its right endpoint.  The support condition is open at
that endpoint, so the atom at the lower endpoint remains visible. -/
def localDeltaAtomization
    (T : RealDistribution) (a δ : ℝ) : Prop :=
  ∃ (m : ℕ) (α : Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℤ),
    α 0 = a ∧
      (∀ j : Fin (m + 1), α j ∈ Set.Ico a (a + δ)) ∧
      (∀ j : Fin (m + 1), c j ≠ 0) ∧
      (∀ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
        tsupport (φ : ℝ → ℝ) ⊆ Set.Iio (a + δ) →
          T φ =
            (∑ j : Fin (m + 1),
              (c j : ℝ) • localDeltaMass (α j)) φ)

/-- Compact distributional shift spectra atomize at a meromorphic edge. -/
def claim15522 : Prop :=
  ∀ (T : RealDistribution) (a : ℝ) (logZeta L : ℂ → ℂ),
    T ≠ 0 →
    IsCompact (Distribution.dsupport T) →
    IsLeast (Distribution.dsupport T) a →
    IsActualShiftedZetaLog T a logZeta L →
    HasNonzeroMeromorphicContinuation a L →
    ∃ δ : ℝ, 0 < δ ∧ localDeltaAtomization T a δ

end

end MathlibPlus.Open.ResearchFormalization.O0338
