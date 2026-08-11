import Mathlib

/-!
# Strict total positivity of weighted moment-curve tables

Statement formalization of admitted claim 167 from legacy packet `C-0010`.
-/

namespace MathlibPlus.Open.MomentCurve

/-- Every square minor of every finite factorial-scaled weighted moment-curve
matrix is positive when rows and columns are selected in their inherited orders,
the nodes are positive and strictly increasing, and the row weights are positive.
This includes the empty minor, whose determinant is one. -/
def strictTotalPositivityWeightedMomentTable : Prop :=
  ∀ (m d r : ℕ) (x w : Fin m → ℝ)
      (rows : Fin r ↪o Fin m) (cols : Fin r ↪o Fin d),
    (∀ i, 0 < x i) → StrictMono x → (∀ i, 0 < w i) →
      0 < Matrix.det (fun i j : Fin r ↦
        w (rows i) * x (rows i) ^ (cols j : Fin d).val /
          (((2 * (cols j : Fin d).val).factorial : ℕ) : ℝ))

end MathlibPlus.Open.MomentCurve
