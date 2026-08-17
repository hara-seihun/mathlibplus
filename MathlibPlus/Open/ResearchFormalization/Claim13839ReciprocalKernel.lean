import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim13839ReciprocalKernel

noncomputable section

/-- The physical reciprocal ray kernel at a positive scale `u`. -/
private def physicalReciprocalKernel13839 (q u : ℝ) : ℝ :=
  Real.rpow u (5 / 4 : ℝ) * Real.exp (-q * u) +
    Real.rpow u (-5 / 4 : ℝ) * Real.exp (-q / u)

/-- Claim 13839: the physical reciprocal kernel at `u = exp t` has the
hyperbolic form and its exact exponential-ray expansion, with only the
physical variables `q` and `t`. -/
def claim13839_reciprocalKernelExponentialExpansion : Prop :=
  ∀ q t : ℝ,
    physicalReciprocalKernel13839 q (Real.exp t) =
        2 * Real.exp (-q * Real.cosh t) *
          Real.cosh (5 / 4 * t - q * Real.sinh t) ∧
      HasSum
        (fun n : ℕ =>
          (2 * (-q) ^ n / (Nat.factorial n : ℝ)) *
            Real.cosh (((n : ℝ) + 5 / 4) * t))
        (physicalReciprocalKernel13839 q (Real.exp t))

end

end MathlibPlus.Open.ResearchFormalization.Claim13839ReciprocalKernel
