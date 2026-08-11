import Mathlib

namespace MathlibPlus.Algebra

open scoped BigOperators

/-- Claim 6424: the elementary-symmetric expansion of a product of shifted
factors, with the elementary symmetric polynomial written as the sum over
subsets of the indicated cardinality. -/
theorem elementarySymmetric_shiftedProduct
    {R : Type*} [CommRing R] (m : ℕ) (G : Fin m → R) (x_d : R) :
    let e : ℕ → R := fun j =>
      ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
        ∏ i ∈ s, G i
    e 0 = 1 ∧
      e (m + 1) = 0 ∧
      ∏ i : Fin m, (x_d + G i) =
        ∑ j ∈ Finset.range (m + 1), x_d ^ (m - j) * e j := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · simp
  · have hempty :
        Finset.powersetCard (m + 1) (Finset.univ : Finset (Fin m)) = ∅ := by
      apply Finset.powersetCard_eq_empty.mpr
      simp
    rw [hempty]
    simp
  · calc
    ∏ i : Fin m, (x_d + G i) =
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          (∏ i ∈ s, G i) * ∏ i ∈ (Finset.univ : Finset (Fin m)) \ s, x_d := by
      simpa [add_comm] using
        (Finset.prod_add (fun i : Fin m => G i) (fun _ => x_d)
          (Finset.univ : Finset (Fin m)))
    _ = ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          (∏ i ∈ s, G i) * x_d ^ (m - s.card) := by
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      rw [Finset.prod_const]
      rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.1 hs)]
      simp
    _ = ∑ j ∈ Finset.range (m + 1),
          ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
            (∏ i ∈ s, G i) * x_d ^ (m - s.card) := by
      rw [Finset.sum_powerset]
      simp
    _ = ∑ j ∈ Finset.range (m + 1),
          x_d ^ (m - j) *
            ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
              ∏ i ∈ s, G i := by
      apply Finset.sum_congr rfl
      intro j hj
      have hcard : ∀ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
          s.card = j := by
        intro s hs
        exact (Finset.mem_powersetCard.1 hs).2
      calc
        ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
              (∏ i ∈ s, G i) * x_d ^ (m - s.card) =
            ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
              (∏ i ∈ s, G i) * x_d ^ (m - j) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hcard s hs]
        _ = (∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
              ∏ i ∈ s, G i) * x_d ^ (m - j) := by
          rw [Finset.sum_mul]
        _ = x_d ^ (m - j) *
              ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
                ∏ i ∈ s, G i := by ring

end MathlibPlus.Algebra
