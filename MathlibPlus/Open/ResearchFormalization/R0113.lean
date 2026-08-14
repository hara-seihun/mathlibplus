import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The tail-incidence matrix appearing in Claim 18039. -/
def tailIncidenceKernel (M n : ℕ) : ℝ :=
  if n ≥ M then 1 else 0

/-- Claim 18039: every finite minor of the tail-incidence kernel is nonnegative. -/
def tailIncidenceKernelTotallyNonnegative : Prop :=
  ∀ (r : ℕ) (M n : Fin r → ℕ),
    StrictMono M →
    StrictMono n →
    0 ≤ Matrix.det (fun i j : Fin r => tailIncidenceKernel (M i) (n j))

end MathlibPlus.Open.ResearchFormalization
