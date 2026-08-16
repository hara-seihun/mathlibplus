import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

noncomputable section

/-- The real smooth compactly supported test space used by the source claim. -/
def realSmoothCompactlySupported (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ f ∧ HasCompactSupport f

/-- The two exponential boundary functionals in the polar term. -/
noncomputable def boundaryA (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.exp (-x / 2)

noncomputable def boundaryB (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.exp (x / 2)

/-- Linear independence of two functionals on the specified test space. -/
def independentOnTestSpace
    (U V : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ a b : ℝ,
    (∀ f : ℝ → ℝ, realSmoothCompactlySupported f →
      a * U f + b * V f = 0) →
    a = 0 ∧ b = 0

/-- The polar boundary form, with the real-valued carrier of the source claim. -/
noncomputable def poleForm (f : ℝ → ℝ) : ℝ :=
  2 * boundaryA f * boundaryB f

/--
The displayed pair of square channels is a `(1,1)` signature when the two
channels are independent on the test space.  The independence clause records
that there is exactly one positive and one negative square, rather than merely
recording that the form takes both signs.
-/
def claim_14933 : Prop :=
  independentOnTestSpace boundaryA boundaryB →
    (∀ f : ℝ → ℝ, realSmoothCompactlySupported f →
      poleForm f =
          2 * Complex.re
            ((boundaryA f : ℂ) * star (boundaryB f : ℂ)) ∧
        poleForm f =
          (1 / 2 : ℝ) * (boundaryA f + boundaryB f) ^ 2 -
            (1 / 2 : ℝ) * (boundaryA f - boundaryB f) ^ 2) ∧
    independentOnTestSpace
      (fun f : ℝ → ℝ => boundaryA f + boundaryB f)
      (fun f : ℝ → ℝ => boundaryA f - boundaryB f)

end

end MathlibPlus.Open.Research.FormalizationBatch
