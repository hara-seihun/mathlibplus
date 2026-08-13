import Mathlib

namespace MathlibPlus.Analysis.Claim47946

open scoped BigOperators

/--
Claim 47946, finite atomic case.  The atoms are indexed in increasing event
order, so `hD` is exactly the condition that the cumulative signed charge is
zero at every event time.  The source's additional compactly-supported-measure
extension is not silently identified with a particular Mathlib measure API.
-/
theorem finiteCausalCompensation
    (N : ℕ) (t a : ℕ → ℝ)
    (_ht_nonneg : ∀ k, k ≤ N → 0 ≤ t k)
    (_ht_strict : ∀ i j, i ≤ N → j ≤ N → i < j → t i < t j)
    (hD : ∀ k, k ≤ N → (∑ j ∈ Finset.range (k + 1), a j) = 0) :
    (∀ k, k ≤ N → a k = 0) ∧
      ∀ z : ℂ, (∑ j ∈ Finset.range (N + 1),
        (a j : ℂ) * Complex.exp (-z * (t j : ℂ))) = 0 := by
  have ha : ∀ k, k ≤ N → a k = 0 := by
    intro k hk
    induction k with
    | zero =>
        simpa using hD 0 (by omega)
    | succ k ih =>
        have hprev := hD k (by omega)
        have hcur := hD (k + 1) hk
        rw [Finset.sum_range_succ] at hcur
        rw [hprev] at hcur
        simpa using hcur
  refine ⟨ha, ?_⟩
  intro z
  apply Finset.sum_eq_zero
  intro j hj
  have hjN : j ≤ N := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [ha j hjN]
  simp

end MathlibPlus.Analysis.Claim47946
