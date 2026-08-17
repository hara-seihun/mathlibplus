import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchO0078

namespace MathlibPlus.Open.ResearchFormalization.BatchO0078.Claim12112

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchO0078

noncomputable def trigammaKernel (a x : ℝ) : ℝ :=
  x * Real.exp (-a * x) / (1 - Real.exp (-x))

noncomputable def trigammaIntegral (a y : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    deriv (deriv (trigammaKernel a)) x * (1 - Real.cos (y * x))

def trigammaKernelShape (a : ℝ) : Prop :=
  (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 < trigammaKernel a x) ∧
    AntitoneOn (trigammaKernel a) (Set.Ioi (0 : ℝ)) ∧
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (trigammaKernel a)

def shiftedTrigammaIntegralIdentity (a y : ℝ) : Prop :=
  y ≠ 0 →
    (trigamma (a - (y : ℂ) * Complex.I)).re =
        (y ^ 2)⁻¹ * trigammaIntegral a y ∧
      0 < trigammaIntegral a y

/-- Positivity of the shifted trigamma clock, together with the displayed
nonzero-imaginary-part integral identity and the stated shape of its kernel. -/
def claim12112 : Prop :=
  ∀ (m : ℕ) (σ t : ℝ),
    1 ≤ m →
    (1 / 2 : ℝ) ≤ σ →
    σ ≤ 1 →
    shiftedClock m σ t > 0 ∧
      trigammaKernelShape ((m : ℝ) + σ / 2) ∧
      shiftedTrigammaIntegralIdentity ((m : ℝ) + σ / 2) (t / 2)

end
end MathlibPlus.Open.ResearchFormalization.BatchO0078.Claim12112
