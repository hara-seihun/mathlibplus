import Mathlib

namespace MathlibPlus.Combinatorics.Claim24379

/-- Disjoint nonsingleton blocks in an `n`-element parent occupy at least `2r` vertices. -/
theorem two_mul_le_parentOrder_of_blocks
    {n r : ℕ} (B : Fin r → Finset (Fin n))
    (hdisj : (Set.univ : Set (Fin r)).PairwiseDisjoint B)
    (hcard : ∀ i : Fin r, 2 ≤ (B i).card) :
    2 * r ≤ n := by
  have hsum : 2 * r ≤ ∑ i : Fin r, (B i).card := by
    calc
      2 * r = ∑ _i : Fin r, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin r, (B i).card := by
        exact Finset.sum_le_sum (fun i _hi => hcard i)
  have hunion : (Finset.univ.biUnion B).card = ∑ i : Fin r, (B i).card := by
    simpa using (Finset.card_biUnion (s := (Finset.univ : Finset (Fin r)))
      (by simpa using hdisj))
  have hle : (∑ i : Fin r, (B i).card) ≤ n := by
    calc
      (∑ i : Fin r, (B i).card) = (Finset.univ.biUnion B).card := hunion.symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  exact hsum.trans hle

/-- The block bound implies the half-order bound for the first surviving degree. -/
theorem firstSurvivingDegree_le_half
    {n r : ℕ} (hr : 1 ≤ r) (hblocks : 2 * r ≤ n) :
    1 ≤ r ∧ r ≤ n / 2 := by
  refine ⟨hr, ?_⟩
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by simpa [Nat.mul_comm] using hblocks)

end MathlibPlus.Combinatorics.Claim24379
