import Mathlib

namespace MathlibPlus.Analysis.Claim4949

/-- A function flag is strict cellular Chebyshev when every strictly selected
set of fibers has a positive evaluation determinant on every increasing cell
transversal. -/
def strictCellularChebyshevFlag_claim4949 (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ (r : ℕ) (j : Fin r → ℕ), StrictMono j →
    ∀ (n : Fin r → ℤ), StrictMono n →
      ∀ (x : Fin r → ℝ),
        (∀ i, x i ∈ Set.Ioo (n i : ℝ) ((n i : ℝ) + 1)) →
          0 < Matrix.det (fun i k => f (j k) (x i))

end MathlibPlus.Analysis.Claim4949
