import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Real.Basic

namespace MathlibPlus.Analysis

/-- The coboundary of an invariant mean vanishes on each invariant orbit.
The displayed consequence in claim 48102 is algebraic, so boundedness,
positivity, and normalization are not needed in this formalization. -/
theorem invariantMeanCoboundary_claim48102
    {V : Type*} [AddCommGroup V]
    (T : ℚ≥0ˣ → V →+ V)
    (_hT_mul : ∀ (r s : ℚ≥0ˣ) (f : V), T (r * s) f = T r (T s f))
    (_hT_one : ∀ f : V, T 1 f = f)
    (M : V →+ ℝ)
    (hM : ∀ (r : ℚ≥0ˣ) (f : V), M (T r f) = M f)
    (r : ℚ≥0ˣ) (f : V) :
    M (T r f) = M f ∧ M (T r f - f) = 0 := by
  constructor
  · exact hM r f
  · calc
      M (T r f - f) = M (T r f) - M f := by
        exact M.map_sub (T r f) f
      _ = 0 := by rw [hM r f, sub_self]

end MathlibPlus.Analysis
