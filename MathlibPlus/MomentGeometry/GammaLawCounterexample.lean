-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

/-!
# Gamma-law counterexample to generic rank propagation

Formalization of admitted claim 372.
-/

namespace MathlibPlus.MomentGeometry

open Matrix
open scoped BigOperators

/-- Exact rank-two positivity, rank-three determinant, and highest-ratio wall
placement for the gamma law `mⱼ = j!`. The completed Bezout matrix uses the
packet normalization `hⱼ = mⱼ/(2j)!`. -/
theorem gammaLawRankPropagationCounterexample :
    let m : ℕ → ℚ := fun j ↦ j.factorial
    let h : ℕ → ℚ := fun j ↦ m j / (2 * j).factorial
    let completedBezout : (N : ℕ) → Matrix (Fin N) (Fin N) ℚ := fun _ i j ↦
      ∑ k ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
        (i + j + 1 - 2 * k : ℕ) * h k * h (i + j + 1 - k)
    let ρ₁ : ℚ := m 0 * m 2 / m 1 ^ 2
    let ρ₂ : ℚ := m 1 * m 3 / m 2 ^ 2
    let ρ₃ : ℚ := m 2 * m 4 / m 3 ^ 2
    let ρ₄ : ℚ := m 3 * m 5 / m 4 ^ 2
    let a : ℚ := 3 * ρ₁ * ρ₂ - 10 * ρ₁ + 15
    let C : ℚ :=
      -180 * ρ₁ ^ 2 * ρ₂ ^ 3 * ρ₃ ^ 2 +
      2520 * ρ₁ ^ 2 * ρ₂ ^ 2 * ρ₃ - 2646 * ρ₁ ^ 2 * ρ₂ ^ 2 -
      2205 * ρ₁ * ρ₂ ^ 2 * ρ₃ - 9450 * ρ₁ * ρ₂ * ρ₃ +
      26460 * ρ₁ * ρ₂ - 14700 * ρ₁ + 14175 * ρ₂ * ρ₃ -
      35280 * ρ₂ + 22050
    let ρ₄star : ℚ := -C / (35 * ρ₁ * ρ₂ ^ 2 * ρ₃ ^ 2 * a)
    0 < (completedBezout 2).det ∧
      36578304000 * (completedBezout 3).det = -1536 ∧
      ρ₄ - ρ₄star = -2 / 35 ∧ ρ₄ - ρ₄star < 0 := by
  native_decide

end MathlibPlus.MomentGeometry

namespace MathlibPlus.Open.MomentGeometry

/-- Every available minor of every finite Stieltjes moment table of the gamma
law `mⱼ=j!` is strictly positive. Order embeddings select rows and columns in
their inherited orders; arbitrary selections include both ordinary and shifted
Hankel minors. -/
def gammaLawStieltjesStrictTotalPositivity : Prop :=
  ∀ (m n r : ℕ) (rows : Fin r ↪o Fin m) (cols : Fin r ↪o Fin n),
    0 < Matrix.det (fun i j : Fin r ↦
      ((((rows i : Fin m).val + (cols j : Fin n).val).factorial : ℕ) : ℚ))

end MathlibPlus.Open.MomentGeometry
