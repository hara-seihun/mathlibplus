import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators
open MeasureTheory

/--
Giving every row its own particle pair, the determinant of the completed
Bezout matrix is the integral of the row-polarized determinant.
-/
def allRankRowPolarizedParticleIdentity : Prop :=
  ∀ (N : ℕ) (μ : Measure NNReal),
    let moment : ℕ → ℝ := fun j => ∫ x : NNReal, (x : ℝ) ^ j ∂μ
    let h : ℕ → ℝ := fun j => moment j / (Nat.factorial (2 * j) : ℝ)
    let C : Matrix (Fin N) (Fin N) ℝ := fun i j =>
      Finset.sum (Finset.range (min (i : ℕ) (j : ℕ) + 1)) (fun a =>
        ((i : ℕ) + (j : ℕ) + 1 - 2 * a) *
          h a * h ((i : ℕ) + (j : ℕ) + 1 - a))
    let κ : ℕ → ℕ → NNReal → NNReal → ℝ := fun i j x y =>
      (1 / 2 : ℝ) *
        Finset.sum (Finset.range (min i j + 1)) (fun a =>
          (((i + j + 1 - 2 * a : ℕ) : ℝ) /
            ((Nat.factorial (2 * a) : ℝ) *
              (Nat.factorial (2 * (i + j + 1 - a)) : ℝ))) *
            ((x : ℝ) ^ a * (y : ℝ) ^ (i + j + 1 - a) +
              (x : ℝ) ^ (i + j + 1 - a) * (y : ℝ) ^ a))
    Matrix.det C =
      ∫ p : (Fin N → NNReal) × (Fin N → NNReal),
        Matrix.det (fun (i j : Fin N) =>
          κ (i : ℕ) (j : ℕ) (p.1 i) (p.2 i)) ∂
          ((Measure.pi (fun _ : Fin N => μ)).prod
            (Measure.pi (fun _ : Fin N => μ)))

end MathlibPlus.Open
