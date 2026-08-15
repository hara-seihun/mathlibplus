import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.ParaorthogonalPolynomialFamily

/--
The paraorthogonal numerator has only simple roots on the unit circle, with
its boundary argument derivative given by the finite-Blaschke root formula.
The statement is intentionally open: its proof belongs to a later admission.
-/
def numeratorHasSimpleUnitCircleRoots : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    let a : ℂ := (1 : ℂ) / (Real.sqrt 2 : ℂ)
    let D : ℕ := 4 * m + 2
    let F : Polynomial ℂ :=
      Finset.sum (Finset.range (m + 1))
        (fun k => Polynomial.C (a ^ k) * Polynomial.X ^ k)
    let H : Polynomial ℂ := F.reverse
    let P : Polynomial ℂ := F + Polynomial.X ^ (D - m) * H
    let B : ℂ → ℂ := fun z => H.eval z / F.eval z
    let rootSum : ℝ → ℝ := fun θ =>
      (H.roots.map (fun α =>
        (1 - ‖α‖ ^ 2) /
          ‖Complex.exp (((θ : ℂ) * Complex.I)) - α‖ ^ 2)).sum
    let boundaryArgumentDerivative : ℝ → ℝ := fun θ =>
      Complex.im (deriv (fun t : ℝ =>
        (Complex.exp (((t : ℂ) * Complex.I))) ^ (D - m) *
          B (Complex.exp (((t : ℂ) * Complex.I)))) θ /
        ((Complex.exp (((θ : ℂ) * Complex.I))) ^ (D - m) *
          B (Complex.exp (((θ : ℂ) * Complex.I)))))
    H.Separable ∧
      H.natDegree = m ∧
      H.roots.card = m ∧
      (∀ α ∈ H.roots, ‖α‖ = ‖a‖) ∧
      P ≠ 0 ∧
      P.natDegree = D ∧
      P.reverse = P ∧
      (∀ z : ℂ, F.eval z ≠ 0 →
        P.eval z = F.eval z * (1 + z ^ (D - m) * B z)) ∧
      (∀ z : ℂ, ‖z‖ < 1 → ¬ P.IsRoot z) ∧
      (∀ z : ℂ, 1 < ‖z‖ → ¬ P.IsRoot z) ∧
      (∀ θ : ℝ,
        boundaryArgumentDerivative θ =
            ((D - m : ℕ) : ℝ) + rootSum θ ∧
          0 < ((D - m : ℕ) : ℝ) + rootSum θ) ∧
      (P.rootSet ℂ).ncard = D ∧
      P.rootSet ℂ ⊆ {z : ℂ | ‖z‖ = 1}

end MathlibPlus.Open.Algebra.ParaorthogonalPolynomialFamily
