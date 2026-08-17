import Mathlib

open scoped Topology
open Set

namespace MathlibPlus.Open.NewResearch2.R0170Repair

noncomputable section

abbrev RankTwoColumn := Fin 2 → ℝ

/-- The affine slope of a rank-two curve in the chart whose first row is
positive. -/
def projectiveSlope (γ : ℝ → RankTwoColumn) (z : ℝ) : ℝ :=
  γ z 1 / γ z 0

/-- The complete projective modulus of four labelled rank-two columns. -/
def fourPointProjectiveModulus
    (y : ℝ → ℝ) (r : Fin 4 → ℝ) : ℝ :=
  ((y (r 2) - y (r 0)) * (y (r 3) - y (r 1))) /
    ((y (r 1) - y (r 0)) * (y (r 3) - y (r 2)))

/-- The ordered four-sample radius domain. -/
def orderedFourSample (r : Fin 4 → ℝ) : Prop :=
  r 0 < r 1 ∧ r 1 < r 2 ∧ r 2 < r 3

/-- A smooth three-coordinate chart for the local ordered fibre of a scalar
four-sample modulus. -/
def smoothThreeDimensionalLocalFiber
    (F : (Fin 4 → ℝ) → ℝ) (r : Fin 4 → ℝ) : Prop :=
  ∃ (U : Set (Fin 4 → ℝ)) (V : Set (Fin 3 → ℝ))
    (φ : (Fin 3 → ℝ) → (Fin 4 → ℝ))
    (ψ : (Fin 4 → ℝ) → (Fin 3 → ℝ)),
    IsOpen U ∧ IsOpen V ∧ r ∈ U ∧ (0 : Fin 3 → ℝ) ∈ V ∧ φ 0 = r ∧
      (∀ v, v ∈ V →
        φ v ∈ U ∧ orderedFourSample (φ v) ∧ F (φ v) = F r) ∧
      (∀ x, x ∈ U → orderedFourSample x → F x = F r →
        ψ x ∈ V ∧ φ (ψ x) = x) ∧
      (∀ v, v ∈ V → ψ (φ v) = v) ∧
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) φ V ∧
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) ψ
        {x | x ∈ U ∧ orderedFourSample x ∧ F x = F r}

/-- Claim 18521: under the rank-two projective carrier and an increasing
nonstationary slope, the four-radius modulus has rank one and regular local
fibres with three independent radius coordinates. -/
def claim18521_localFiberNonidentifiability : Prop :=
  ∀ (γ : ℝ → RankTwoColumn),
    (∀ z : ℝ, 0 < γ z 0) →
    let y := projectiveSlope γ
    StrictMono y ∧
      (∀ z : ℝ, DifferentiableAt ℝ y z ∧ deriv y z ≠ 0) →
      ∀ r : Fin 4 → ℝ,
        orderedFourSample r →
        let X := fourPointProjectiveModulus y
        DifferentiableAt ℝ X r ∧
          Module.finrank ℝ
              ((fderiv ℝ X r).toLinearMap.range) = 1 ∧
          smoothThreeDimensionalLocalFiber X r ∧
          ∃ U : Set (Fin 4 → ℝ),
            IsOpen U ∧ r ∈ U ∧
              ∃ r' : Fin 4 → ℝ,
                r' ∈ U ∧ orderedFourSample r' ∧ r' ≠ r ∧ X r' = X r

end

end MathlibPlus.Open.NewResearch2.R0170Repair
