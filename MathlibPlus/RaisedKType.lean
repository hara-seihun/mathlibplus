import Mathlib

/-!
# Raised K-type finite phase sums

An exact finite-sum identity extracted from legacy packet `C-0019`.  This module
formalizes only the packet's elementary scalar calculation; it introduces none of
the unresolved automorphic placeholder objects from the same packet.
-/

namespace MathlibPlus.RaisedKType

/-- The exact linear sum underlying the accumulated phase-error expansion:
`∑_{r<m} (A_r + B_r) / t = 2m(k+m)/t`, where
`A_r = k + 2r + 1/2` and `B_r = k + 2r + 3/2`. -/
theorem backwardPhaseLinearSum (k m : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (∑ r ∈ Finset.range m,
        (((k : ℝ) + 2 * (r : ℝ) + 1 / 2) +
          ((k : ℝ) + 2 * (r : ℝ) + 3 / 2)) / t) =
      2 * (m : ℝ) * ((k : ℝ) + (m : ℝ)) / t := by
  rw [← Finset.sum_div]
  field_simp
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [ih]
      ring

end MathlibPlus.RaisedKType
