import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable def gaussianDilationKernel (t : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (5 * t / 2) * Real.exp (-Real.pi * Real.exp (2 * t))

def strictlyTotallyPositive (k : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ x y : Fin n → ℝ,
      StrictMono x → StrictMono y →
        0 < Matrix.det (fun i j => k (x i - y j))

noncomputable def claim18367 : Prop := strictlyTotallyPositive gaussianDilationKernel

noncomputable def claim18368 : Prop :=
  ∀ z : ℂ, (-5 / 2 : ℝ) < z.re →
    Integrable
        (fun t : ℝ =>
          Complex.exp (z * (t : ℂ)) * (gaussianDilationKernel t : ℂ))
        volume ∧
      ∫ t : ℝ,
          Complex.exp (z * (t : ℂ)) * (gaussianDilationKernel t : ℂ) =
        (Real.pi : ℂ) ^ ((-1 / 4 : ℂ) - z / 2) *
          Complex.Gamma (5 / 4 + z / 2)

noncomputable def claim18369 : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    let integrand : ℝ → ℂ := fun x =>
      ((Int.fract x : ℝ) : ℂ) * Complex.cpow (x : ℂ) (-s - 1)
    Integrable integrand (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∫ x in Set.Ioi (0 : ℝ), integrand x) = -riemannZeta s / s

end MathlibPlus.Open.Analysis
