import Mathlib

open Set
open scoped BigOperators

namespace MathlibPlus.LinearAlgebra.Claim17286

/-- The positive-semidefinite region of an affine matrix line, restricted to
positive parameters, is an interval.  This is the matrix-level formalization
of the one-channel positivity-set claim; no symmetry or finite-index
hypothesis is added. -/
theorem oneChannelPositivitySet_isInterval
    {n : Type*} (A B : Matrix n n ℝ) :
    Convex ℝ {x : ℝ | 0 < x ∧ (A + x • B).PosSemidef} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxpos, hxpsd⟩
  rcases hy with ⟨hypos, hypsd⟩
  constructor
  · positivity
  · have hsum :
        (a • (A + x • B) + b • (A + y • B)).PosSemidef :=
      (hxpsd.smul ha.le).add (hypsd.smul hb.le)
    have hmat :
        A + (a • x + b • y) • B =
          a • (A + x • B) + b • (A + y • B) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      calc
        _ = (a + b) * A i j + (a * x + b * y) * B i j := by
          rw [hab]
          ring
        _ = a * (A i j + x * B i j) + b * (A i j + y * B i j) := by
          ring
    rw [hmat]
    exact hsum

/-- Equivalently, the positivity region is order-connected, hence an interval
(possibly empty or unbounded). -/
theorem oneChannelPositivitySet_ordConnected
    {n : Type*} (A B : Matrix n n ℝ) :
    ({x : ℝ | 0 < x ∧ (A + x • B).PosSemidef} : Set ℝ).OrdConnected :=
  (oneChannelPositivitySet_isInterval A B).ordConnected

end MathlibPlus.LinearAlgebra.Claim17286
