import Mathlib

open scoped BigOperators Filter FourierTransform Topology
open MeasureTheory Filter
noncomputable section

namespace MathlibPlus.Open.Analysis.Claim13344FiniteL1NoGo

noncomputable def realFourierTransform (a : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ,
    Complex.exp (-(2 * Real.pi * (x * t)) * Complex.I) * (a x : ℂ)

noncomputable def realConvolution
    (a q : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ x : ℝ, a x * q (u - x)

def channelFourierEnergy {m : ℕ}
    (a : Fin m → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin m, ‖realFourierTransform (a j) t‖ ^ 2

noncomputable def channelL2Norm {m : ℕ}
    (a : Fin m → ℝ → ℝ) (q : ℝ → ℝ) : ℝ :=
  Real.sqrt (∑ j : Fin m,
    (lpNorm (fun u : ℝ => realConvolution (a j) q u) 2 volume) ^ 2)

/-- Claim 13344: finite critically normalized L1 kernels have vanishing
Fourier energy at infinity and their convolution analysis map is not bounded
below on L2. -/
def claim13344_generalFiniteL1ChannelNoGo : Prop :=
  ∀ (m : ℕ) (a : Fin m → ℝ → ℝ),
    (∀ j : Fin m, Integrable (a j) volume) →
      (∀ j : Fin m,
        Tendsto (realFourierTransform (a j))
          (cocompact ℝ) (𝓝 0)) ∧
      Tendsto (channelFourierEnergy a)
        (cocompact ℝ) (𝓝 0) ∧
      ¬∃ c : ℝ, 0 < c ∧
        ∀ q : ℝ → ℝ, MemLp q 2 volume →
          c * lpNorm q 2 volume ≤ channelL2Norm a q

end MathlibPlus.Open.Analysis.Claim13344FiniteL1NoGo
