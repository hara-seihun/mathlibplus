import Mathlib

namespace MathlibPlus.Analysis.R0438

/-- The pressure kernel in Claim 21366. -/
noncomputable def pressureKernel21366 (u : ℝ) : ℝ :=
  1 / (u * (u + 1))

/-- Claim 21366: the pressure kernel has the displayed first and second
 derivatives on the positive half-line, and is strictly decreasing and
 strictly convex there. -/
def pressureKernelMonotonicityConvexity_claim21366 : Prop :=
  (∀ u : ℝ, 0 < u →
    deriv pressureKernel21366 u =
      -(2 * u + 1) / (u ^ 2 * (u + 1) ^ 2) ∧
    deriv (fun x => deriv pressureKernel21366 x) u =
      2 * (3 * u ^ 2 + 3 * u + 1) /
        (u ^ 3 * (u + 1) ^ 3)) ∧
  StrictAntiOn pressureKernel21366 (Set.Ioi 0) ∧
  StrictConvexOn ℝ (Set.Ioi 0) pressureKernel21366

end MathlibPlus.Analysis.R0438
