import Mathlib

namespace MathlibPlus.Analysis.Claim4629

open scoped BigOperators

/-!
A finite shift measure is represented by finitely many real atoms `x i` and
real weights `w i`.  This retains the mass, first-moment, and balancedness
parts of the source without assuming an unprovided measure-theory interface.
-/

/-- Translation preserves mass, transforms the first moment by `a * mass`, and
preserves the zero-mass/zero-first-moment balance condition. -/
theorem finite_shift_measure_moments_claim4629
    {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (a : ℝ) :
    let mass := ∑ i : ι, w i
    let m₁ := ∑ i : ι, w i * x i
    let shiftedMass := ∑ i : ι, w i
    let shiftedM₁ := ∑ i : ι, w i * (x i + a)
    shiftedMass = mass ∧
      shiftedM₁ = m₁ + a * mass ∧
      (mass = 0 ∧ m₁ = 0 → shiftedM₁ = 0) := by
  dsimp
  have hmom :
      (∑ i : ι, w i * (x i + a)) =
        (∑ i : ι, w i * x i) + a * ∑ i : ι, w i := by
    calc
      (∑ i : ι, w i * (x i + a)) =
          ∑ i : ι, (w i * x i + a * w i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : ι, w i * x i) + ∑ i : ι, a * w i :=
        Finset.sum_add_distrib
      _ = (∑ i : ι, w i * x i) + a * ∑ i : ι, w i := by
        congr 1
        rw [Finset.mul_sum]
  refine ⟨rfl, hmom, ?_⟩
  rintro ⟨hmass, hm₁⟩
  rw [hmom, hm₁, hmass]
  ring

end MathlibPlus.Analysis.Claim4629
