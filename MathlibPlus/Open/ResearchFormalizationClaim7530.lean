import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch

/--
Scarweave susceptibility has a negative two-temperature determinant, which is
the obstruction to the proposed finite-temperature Gram kernel.
-/
def claim7530_scarweaveSusceptibilityNotGramKernel : Prop :=
  let zetaTerm : ℝ → ℕ → ℝ := fun σ n =>
    if 1 ≤ n then (n : ℝ) ^ (-σ) else 0
  let zeta : ℝ → ℝ := fun σ => ∑' n : ℕ, zetaTerm σ n
  let gibbsWeight : ℝ → ℕ → ℝ := fun σ n =>
    if 1 ≤ n then zetaTerm σ n / zeta σ else 0
  let A : ℝ → ℝ := fun σ =>
    ∑' n : ℕ, Real.log (n : ℝ) * gibbsWeight σ n
  let V : ℝ → ℝ := fun σ =>
    (∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * gibbsWeight σ n) - (A σ) ^ 2
  let D_SW : ℝ → ℝ → ℝ := fun lam mu =>
    if lam = mu then
      (A (1 / 2 + lam) + lam * V (1 / 2 + lam)) / (2 * lam ^ 3)
    else
      let r := min lam mu
      let R := max lam mu
      (A (1 / 2 + r) + r *
          ((R - r)⁻¹ * (∫ t in r..R, V (1 / 2 + t))) /
        (r * R * (r + R)))
  ∃ lam₁ lam₂ : ℝ,
    1 / 2 < lam₁ ∧
    1 / 2 < lam₂ ∧
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![D_SW lam₁ lam₁, D_SW lam₁ lam₂;
         D_SW lam₂ lam₁, D_SW lam₂ lam₂]
    Matrix.det M < 0

end MathlibPlus.Open.ResearchFormalizationLargeBatch
