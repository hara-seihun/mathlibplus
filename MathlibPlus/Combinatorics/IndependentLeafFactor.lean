import Mathlib

namespace MathlibPlus.Combinatorics.IndependentLeafFactor

/-- Claim 6521: summing one or more independent attached-leaf states factors
through the one-leaf factor `lambda s`.  The state set is exactly
`{0, ..., m}`, represented by `Fin (m + 1)`. -/
theorem attachedLeafStateFactor {m k : ℕ} {R : Type*} [CommSemiring R]
    (q : Fin (m + 1) → Fin (m + 1) → R) (w : Fin (m + 1) → R)
    (s : Fin (m + 1)) (old : R) :
    let lambda : Fin (m + 1) → R := fun s => ∑ t, q s t * w t
    (∑ t, old * (q s t * w t)) = old * lambda s ∧
      (∑ x : Fin k → Fin (m + 1),
        old * ∏ i, (q s (x i) * w (x i))) = old * (lambda s) ^ k := by
  dsimp
  constructor
  · rw [Finset.mul_sum]
  · rw [← Finset.mul_sum]
    have hsum :
        (∑ x : Fin k → Fin (m + 1),
          ∏ i, (q s (x i) * w (x i))) =
          ∏ i : Fin k, ∑ t : Fin (m + 1), q s t * w t := by
      simpa using
        (Fintype.prod_sum (ι := Fin k) (κ := fun _ : Fin k => Fin (m + 1))
          (fun _ t => q s t * w t)).symm
    rw [hsum]
    simp

end MathlibPlus.Combinatorics.IndependentLeafFactor
