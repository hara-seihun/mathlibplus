import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MathlibPlus.Open.Analysis

open BigOperators

/--
Claim 12405: the exponential directions with exponents `2m + 1/2` are
independent on every nonempty open positive interval, together with the
explicit Wronskian/Vandermonde identity.  The Wronskian convention here has
functions as rows and derivative order as columns.
-/
def exponentialDirectionsIndependent : Prop :=
  let phi : ℕ → ℝ → ℝ := fun m x =>
    Real.exp (-((2 * (m : ℝ) + 1 / 2) * x))
  let W : ℕ → ℝ → ℝ := fun r x =>
    Matrix.det (fun i j : Fin r => iteratedDeriv (j : ℕ) (phi i) x)
  (∀ r : ℕ, ∀ a b : ℝ, 0 ≤ a → a < b →
    LinearIndependent ℝ
      (fun i : Fin r => fun x : Set.Ioo a b => phi i (x : ℝ))) ∧
    (∀ r : ℕ, ∀ x : ℝ,
      W r x =
          (∏ i : Fin r, phi i x) *
            ∏ i : Fin r, ∏ j ∈ Finset.univ.filter (fun j : Fin r => i < j),
              (-(2 * (j : ℝ) + 1 / 2) - (-(2 * (i : ℝ) + 1 / 2))) ∧
        W r x ≠ 0)

end MathlibPlus.Open.Analysis
