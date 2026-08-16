import Mathlib
import MathlibPlus.Analysis.ReciprocalXi
import MathlibPlus.Open.Analysis.FormalizationBatchCone13602

namespace MathlibPlus.Open.Analysis.O0125

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The centered entire xi function used by the squared-coordinate
construction. -/
noncomputable def centeredXi : ℂ → ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.centeredXi

/-- The actual entire squared-coordinate function: its square pullback is the
centered xi function. -/
def actualSquaredCoordinate (psi : ℂ → ℂ) : Prop :=
  Differentiable ℂ psi ∧
    (∀ w : ℂ, psi (w ^ 2) = centeredXi w)

/-- The scalar reciprocal relation on the nonnegative Laplace domain. -/
def reciprocalOnNonnegative (psi : ℂ → ℂ) (g : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 ≤ a →
    (g a : ℂ) = psi 0 / psi (a : ℂ)

/-- The projectively consistent, unitarily invariant PSD cone law with iid
scalar diagonals and scalar Laplace transform `g`, using the exact carriers of
Claim 13602. -/
def scalarConeLaw (g : ℝ → ℝ)
    (μ : ∀ m : ℕ, Measure (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  (∀ m : ℕ,
      (μ m) Set.univ = 1 ∧
        (μ m) {B |
          MathlibPlus.Open.Analysis.FormalizationBatchCone13602.positiveHermitian m B} =
          (μ m) Set.univ) ∧
    (∀ r m : ℕ, ∀ h : r ≤ m,
      Measure.map
          (MathlibPlus.Open.Analysis.FormalizationBatchCone13602.leadingCorner h)
          (μ m) = μ r) ∧
    (∀ m : ℕ, ∀ U : Matrix (Fin m) (Fin m) ℂ,
      MathlibPlus.Open.Analysis.FormalizationBatchCone13602.unitaryMatrix m U →
        Measure.map
            (MathlibPlus.Open.Analysis.FormalizationBatchCone13602.conjugateMatrix U)
            (μ m) = μ m) ∧
    (let ν : Measure ℝ :=
      Measure.map
        (fun B : Matrix (Fin 1) (Fin 1) ℂ =>
          Complex.re (B (0 : Fin 1) (0 : Fin 1)))
        (μ 1)
     (∀ m : ℕ,
       MathlibPlus.Open.Analysis.FormalizationBatchCone13602.diagonalMeasure (μ m) =
         Measure.pi (fun _ : Fin m => ν)) ∧
     (∀ a : ℝ, 0 ≤ a →
       MeasureTheory.integral ν (fun b =>
         Complex.exp (-(Complex.ofReal (a * b)))) =
           Complex.ofReal (g a)))

/-- Claim 13603: the scalar cone law first yields the reciprocal product with
negative exponential sign, and analytic continuation through the actual entire
squared-coordinate xi function yields the reciprocal product's inverse.  The
positive factors then force every zero of `Psi` to be a negative real
reciprocal factor. -/
def claim_13603 : Prop :=
  ∃ psi : ℂ → ℂ,
    actualSquaredCoordinate psi ∧
      ∀ (g : ℝ → ℝ)
        (μ : ∀ m : ℕ, Measure (Matrix (Fin m) (Fin m) ℂ)),
        reciprocalOnNonnegative psi g →
        scalarConeLaw g μ →
        ∃ (ι : Type*) (hι : Countable ι) (x : ι → ℝ) (c : ℝ),
          letI := hι
          0 ≤ c ∧
            (∀ k : ι, 0 < x k) ∧
            Summable x ∧
            (∀ a : ℝ, 0 ≤ a →
              g a = Real.exp (-c * a) *
                ∏' k : ι, (1 + x k * a)⁻¹) ∧
            (∀ z : ℂ,
              psi z / psi 0 =
                Complex.exp ((c : ℂ) * z) *
                  ∏' k : ι, (1 + (x k : ℂ) * z)) ∧
            (∀ z : ℂ, psi z = 0 →
              ∃ k : ι,
                z = -((x k : ℂ)⁻¹) ∧
                  z.re < 0 ∧ z.im = 0)

end

end MathlibPlus.Open.Analysis.O0125
