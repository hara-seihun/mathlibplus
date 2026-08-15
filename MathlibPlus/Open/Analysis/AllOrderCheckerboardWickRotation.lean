import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable def centeredRankinQ (α : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 =>
      Polynomial.X * (centeredRankinQ α n).derivative +
        (Polynomial.C (α / 2) - (1 / 2 : ℝ) • Polynomial.X) *
          centeredRankinQ α n

noncomputable def centeredRankinQValue (α : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (centeredRankinQ α n).eval u

noncomputable def centeredRankinRadialWeight (α u : ℝ) : ℝ :=
  Real.rpow u (α - 1) * Real.exp (-u) / Real.Gamma α

noncomputable def centeredRankinInner (α : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), f u * g u * centeredRankinRadialWeight α u

noncomputable def balancedRankinGram (α : ℝ) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j =>
    (centeredRankinInner α (centeredRankinQValue α (i : ℕ))
      (centeredRankinQValue α (j : ℕ)) : ℝ)

noncomputable def oneSidedRankinHankel (α : ℝ) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j =>
    (centeredRankinInner α (fun _ => 1)
      (centeredRankinQValue α ((i : ℕ) + (j : ℕ))) : ℝ)

noncomputable def meixnerPollaczekDensity (α t : ℝ) : ℝ :=
  Real.rpow 2 α *
      ‖Complex.Gamma ((α / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 /
    (2 * Real.pi * Real.Gamma α)

noncomputable def meixnerPollaczekMeasure (α : ℝ) : Measure ℝ :=
  Measure.withDensity volume (fun t =>
    ENNReal.ofReal (meixnerPollaczekDensity α t))

noncomputable def momentGram (α : ℝ) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j =>
    (∫ t : ℝ, t ^ ((i : ℕ) + (j : ℕ)) ∂(meixnerPollaczekMeasure α) : ℝ)

noncomputable def wickDiagonal (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => if i = j then Complex.I ^ (i : ℕ) else 0

noncomputable def complexPositiveSemidefinite {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ) : Prop :=
  (∀ i j, M i j = star (M j i)) ∧
    ∀ v : n → ℂ,
      0 ≤ (∑ i, ∑ j, star (v i) * M i j * v j).re

noncomputable def allOrderCheckerboardWickRotationClaim : Prop :=
  ∀ (α : ℝ), 0 < α → ∀ (m : ℕ),
    let C := wickDiagonal m
    let H := oneSidedRankinHankel α m
    let G := balancedRankinGram α m
    let M := momentGram α m
    C * H * C = M ∧
      complexPositiveSemidefinite (C * H * C) ∧
      C * H * C = Matrix.conjTranspose C * G * C

end MathlibPlus.Open.Analysis
