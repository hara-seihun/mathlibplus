import Mathlib

namespace MathlibPlus.Algebra.Claim59119

/-- The one-way-sector counterexample from claim 59119: the local image of
one forced coordinate is `{1}`, while the signed span of its copy column
already contains `-1`. -/
theorem orientationIncompleteness
    (q : ℝ → ℝ) (hq : q 1 = 1) :
    q '' ({1} : Set ℝ) = ({1} : Set ℝ) ∧
      (-1 : ℝ) ∈ Submodule.span ℝ ({q 1} : Set ℝ) ∧
      (-1 : ℝ) ∉ q '' ({1} : Set ℝ) := by
  have himage : q '' ({1} : Set ℝ) = ({1} : Set ℝ) := by
    rw [Set.image_singleton]
    simp [hq]
  refine ⟨himage, ?_, ?_⟩
  · rw [hq]
    have hone : (1 : ℝ) ∈ Submodule.span ℝ ({(1 : ℝ)} : Set ℝ) :=
      Submodule.subset_span (by simp)
    exact Submodule.neg_mem _ hone
  · rw [himage]
    norm_num

end MathlibPlus.Algebra.Claim59119
