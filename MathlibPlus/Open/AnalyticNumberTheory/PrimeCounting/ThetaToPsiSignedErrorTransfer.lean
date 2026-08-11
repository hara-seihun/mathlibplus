import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
# Theta-to-psi signed-error transfer

Statement-fidelity registry node for admitted claim 772.  The transfer is
pointwise and signed; no absolute-value or lower-error conclusion is added.
-/

/-- Order of theta and psi, and transfer of every pointwise signed upper bound. -/
noncomputable def thetaToPsiSignedErrorTransfer : Prop :=
  (∀ x : ℝ, 0 < x →
    Chebyshev.theta x ≤ Chebyshev.psi x ∧
      (Chebyshev.theta x - x) / x ≤ (Chebyshev.psi x - x) / x) ∧
    (∀ (bound : ℝ → ℝ) (x : ℝ), 0 < x →
      (Chebyshev.psi x - x) / x ≤ bound x →
      (Chebyshev.theta x - x) / x ≤ bound x)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
