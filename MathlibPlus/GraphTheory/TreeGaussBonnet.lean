import Mathlib

namespace MathlibPlus.GraphTheory

/-- Claim 5173: degree balance for a finite tree and the resulting doubled
Euler-curvature sum, with `χ_C(v)` expanded as `2 - deg_C(v)` in `ℤ`. -/
theorem treeDegreeBalanceAndGaussBonnet_claim5173
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) [DecidableRel C.Adj] (hC : C.IsTree) :
    (∑ v, C.degree v = 2 * (Fintype.card V - 1)) ∧
      (∑ v, ((2 : ℤ) - (C.degree v : ℤ)) = 2) := by
  have hEdges := hC.card_edgeFinset
  have hcard : C.edgeFinset.card = Fintype.card V - 1 := by
    omega
  have hVpos : 1 ≤ Fintype.card V := by
    omega
  have hsum := C.sum_degrees_eq_twice_card_edges
  have hsumZ : (∑ v, (C.degree v : ℤ)) = 2 * (C.edgeFinset.card : ℤ) := by
    exact_mod_cast hsum
  constructor
  · rw [hsum, hcard]
  · calc
      ∑ v, ((2 : ℤ) - (C.degree v : ℤ)) =
          (∑ v, (2 : ℤ)) - ∑ v, (C.degree v : ℤ) := by
            rw [Finset.sum_sub_distrib]
      _ = (Fintype.card V : ℤ) * 2 - 2 * (C.edgeFinset.card : ℤ) := by
            rw [hsumZ]
            simp
      _ = 2 := by
            rw [hcard, Nat.cast_sub hVpos]
            ring

end MathlibPlus.GraphTheory
