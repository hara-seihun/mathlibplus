import Mathlib

namespace MathlibPlus.Algebra

/-- The fixed-reference span inequality is equivalent to its error-coordinate
form after substituting `x = c + e`. -/
theorem fixed_reference_span_iff_claim21429
    (c e x : ℕ → ℤ) (L : ℤ) (k r : ℕ) (hr : r ≤ k)
    (hinc : StrictMono c) (hx : ∀ j, x j = c j + e j) :
    x (k + r + 1) - x (k - r) ≤
        L * (x (k + 1) - x k) ↔
      e (k + r + 1) - e (k - r) - L * (e (k + 1) - e k) ≤
        L * (c (k + 1) - c k) - (c (k + r + 1) - c (k - r)) := by
  have hidentity :
      (e (k + r + 1) - e (k - r) - L * (e (k + 1) - e k)) -
          (L * (c (k + 1) - c k) - (c (k + r + 1) - c (k - r))) =
        (c (k + r + 1) + e (k + r + 1) -
            (c (k - r) + e (k - r))) -
          L * ((c (k + 1) + e (k + 1)) - (c k + e k)) := by
    ring
  simp only [hx]
  constructor
  · intro h
    apply (sub_nonpos.mp ?_)
    rw [hidentity]
    exact sub_nonpos.mpr h
  · intro h
    have h' :
        (c (k + r + 1) + e (k + r + 1) -
            (c (k - r) + e (k - r))) -
          L * ((c (k + 1) + e (k + 1)) - (c k + e k)) ≤ 0 := by
      rw [← hidentity]
      exact sub_nonpos.mpr h
    exact sub_nonpos.mp h'

end MathlibPlus.Algebra
