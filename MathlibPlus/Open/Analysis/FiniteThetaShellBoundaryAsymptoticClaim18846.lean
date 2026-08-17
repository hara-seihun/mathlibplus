import Mathlib
import MathlibPlus.Open.Analysis.FiniteThetaShellBoundaryBatch

open scoped BigOperators
open Filter

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 18846: the uncancelled boundary jet controls the real-axis
 asymptotic of every finite theta-shell cosine transform. -/
noncomputable def finiteThetaShellBoundaryAsymptotic_claim18846 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    let phiN : ℝ → ℝ := fun u =>
      Finset.sum (Finset.range N) (fun m =>
        MathlibPlus.Analysis.ThetaMellin.thetaShell (m + 1) u)
    let XN : ℂ → ℂ := fun z =>
      2 * ∫ u in Set.Ioi (0 : ℝ),
        (phiN u : ℂ) * Complex.cos (z * (u : ℂ))
    Asymptotics.IsBigO (Filter.atTop : Filter ℝ)
      (fun t : ℝ =>
        XN (t : ℂ) -
          ((-2 * deriv phiN 0 / t ^ 2 : ℝ) : ℂ))
      (fun t : ℝ => (((t : ℂ)⁻¹) ^ (4 : ℕ)))

end

end MathlibPlus.Open.Analysis
