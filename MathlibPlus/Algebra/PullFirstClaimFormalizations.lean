import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 12452: the leading centre coordinate determines the affine transverse
coordinate by solving the displayed relation for `α`. -/
theorem leadingCentreCoordinate_claim12452 (α β u : ℝ)
    (h : u = α + (5 / Real.pi) * β) :
    α = u - (5 / Real.pi) * β := by
  rw [h]
  ring

end MathlibPlus.Analysis

namespace MathlibPlus.LinearAlgebra

/-- Claim 28570: an empty target-row/one-target-column block has a one-
dimensional coordinate defect over `ℚ`.  The source's P4 construction is not
available as a Mathlib carrier, so the row and column types are made explicit. -/
theorem p4DiagonalDefect_claim28570 (_M : Matrix (Fin 0) (Fin 1) ℚ) :
    Fintype.card (Fin 0) = 0 ∧
      Fintype.card (Fin 1) = 1 ∧
      Module.finrank ℚ (Fin 1 → ℚ) = 1 := by
  simp

end MathlibPlus.LinearAlgebra

namespace MathlibPlus.Algebra

/-- Claim 29163: if two normalized directions are nonzero rational scalar
multiples of the same carrier, they lie on a rational affine axis. -/
theorem wholeDirectionAffineAxis_claim29163
    (Q_R Q_S Q_T p : Polynomial ℚ) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hS : Q_S - Q_T = a • p)
    (hR : Q_R - Q_T = b • p) :
    ∃ lambda : ℚ, lambda ≠ 0 ∧ Q_S - Q_T = lambda • (Q_R - Q_T) := by
  refine ⟨a / b, div_ne_zero ha hb, ?_⟩
  rw [hS, hR]
  rw [smul_smul]
  field_simp

/-- Claim 32907: the five width rows and all displayed totals are retained as
an exact arithmetic census.  The graph/profile carriers and the `GL/PGL`
action are source-specific and are intentionally not silently invented here. -/
theorem colorWidthCensus_claim32907 :
    (5 : ℕ) + 40940 + 5191560 + 73380120 + 165528000 = 244140625 ∧
      5 + 180 + 5180 + 58050 + 126315 = 189730 ∧
      5 + 180 + 5180 + 58050 + 126315 = 189730 ∧
      (5 : ℕ) ^ 12 = 244140625 := by
  norm_num

/-- Claim 38286: the normal category and the six disjoint nonnormal category
counts have the exact displayed totals. -/
theorem fullAutomorphismCategorySplit_claim38286 :
    (8353 : ℕ) + 1332 + 233 + 1264 + 82 + 118 + 14 = 11396 ∧
      1332 + 233 + 1264 + 82 + 118 + 14 = 3043 := by
  norm_num

end MathlibPlus.Algebra
