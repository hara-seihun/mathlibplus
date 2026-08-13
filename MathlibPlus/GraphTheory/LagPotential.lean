import Mathlib

namespace MathlibPlus.GraphTheory

/-- Claim 49852.  A difference potential makes the total weight of every
finite permutation union of active directed lag cycles nonpositive.  A single
cycle is the special case in which the permutation has one orbit. -/
theorem lagCycleWeight_nonpos_of_potential_claim49852
    {ι : Type*} [Fintype ι]
    (active : ι → ι → Prop)
    (upsilon : ι → ι → ℝ) (r : ι → ℝ)
    (hpotential : ∀ {j i}, active j i → upsilon j i ≤ r i - r j)
    (next : ι → ι) (hbij : Function.Bijective next)
    (hactive : ∀ i, active i (next i)) :
    (∑ i, upsilon i (next i)) ≤ 0 := by
  classical
  have hterm : ∀ i, upsilon i (next i) ≤ r (next i) - r i := by
    intro i
    exact hpotential (hactive i)
  have hsum :
      (∑ i, upsilon i (next i)) ≤ ∑ i, (r (next i) - r i) :=
    Finset.sum_le_sum (fun i hi => hterm i)
  have hnext : (∑ i, r (next i)) = ∑ i, r i := by
    exact Equiv.sum_comp (Equiv.ofBijective next hbij) r
  calc
    (∑ i, upsilon i (next i)) ≤ ∑ i, (r (next i) - r i) := hsum
    _ = (∑ i, r (next i)) - ∑ i, r i := by
      simpa using
        (Finset.sum_sub_distrib (s := (Finset.univ : Finset ι))
          (fun i => r (next i)) (fun i => r i))
    _ = 0 := by rw [hnext]; exact sub_self _

end MathlibPlus.GraphTheory
