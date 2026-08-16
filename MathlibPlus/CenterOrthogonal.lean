import Mathlib

/-!
# Center-orthogonal quartic profile

Exact definitions and elementary consequences extracted from source record `C-0162`.
The predicate `HasSecondFourthMoments` makes the packet's phrase “has second and
fourth moments” explicit: both moment integrands are Bochner-integrable, in addition
to having the displayed values.
-/

open MeasureTheory

namespace MathlibPlus.CenterOrthogonal

noncomputable section

/-- The center-orthogonal quartic profile from packet `C-0162`. -/
def quarticProfile (beta x : ℝ) : ℝ :=
  beta * (x ^ 4 - (5 / Real.pi) * x ^ 2)

/-- The exact second and fourth moment data used by the center-orthogonal
cancellation. Integrability is included in the meaning of “has moments”. -/
def HasSecondFourthMoments (h : ℝ → ℝ) : Prop :=
  Integrable (fun x : ℝ => x ^ 2 * h x) ∧
  Integrable (fun x : ℝ => x ^ 4 * h x) ∧
  (∫ x : ℝ, x ^ 2 * h x) = 3 / (2 * Real.pi ^ 2) ∧
  (∫ x : ℝ, x ^ 4 * h x) = 15 / (2 * Real.pi ^ 3)

/-- The quartic profile cancels against every weight with the packet's exact second
and fourth moments. -/
theorem quarticProfile_momentCancellation (h : ℝ → ℝ)
    (hh : HasSecondFourthMoments h) (beta : ℝ) :
    (∫ x : ℝ, quarticProfile beta x * h x) = 0 := by
  rcases hh with ⟨h2, h4, hm2, hm4⟩
  calc
    (∫ x : ℝ, quarticProfile beta x * h x) =
        ∫ x : ℝ,
          beta * (x ^ 4 * h x) - (beta * (5 / Real.pi)) * (x ^ 2 * h x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [quarticProfile]
      ring
    _ = beta * (∫ x : ℝ, x ^ 4 * h x) -
          (beta * (5 / Real.pi)) * (∫ x : ℝ, x ^ 2 * h x) := by
      rw [integral_sub (h4.const_mul beta) (h2.const_mul (beta * (5 / Real.pi)))]
      simp only [integral_const_mul]
    _ = 0 := by
      rw [hm2, hm4]
      field_simp [ne_of_gt Real.pi_pos]
      ring

/-- The exact endpoint/Poisson–Dini coefficient attached to a selected center value. -/
def poissonDiniCoefficient (q0 : ℝ → ℝ → ℝ) (lambda beta : ℝ) : ℝ :=
  -q0 lambda beta / (2 * Real.sqrt lambda)

/-- Any full Mellin family that factors pointwise through `Xi` preserves every zero
of `Xi`. This is the exact algebraic consequence isolated in packet `C-0162`; it does
not assert that the packet's analytic family has such a factorization. -/
theorem fullMellin_preservesXiZeros
    (Xi : ℂ → ℂ) (F : ℝ → ℝ → ℂ → ℂ)
    (hfactor : ∃ H : ℝ → ℝ → ℂ → ℂ,
      ∀ lambda beta z, F lambda beta z = Xi z * H lambda beta z)
    (lambda beta : ℝ) (z : ℂ) (hz : Xi z = 0) :
    F lambda beta z = 0 := by
  obtain ⟨H, hH⟩ := hfactor
  rw [hH, hz, zero_mul]

end

end MathlibPlus.CenterOrthogonal
