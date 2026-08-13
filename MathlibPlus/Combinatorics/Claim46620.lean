import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim46620

/-- If distinct finite supports are either empty or have size at least two,
then their total support size is at least twice the number of members minus two.
The finite support family models the active chain-block family; no separate
chain-block indexing convention is supplied by the source claim. -/
theorem support_card_sum_lower_bound
    {X : Type*} (F : Finset (Finset X))
    (hsize : ∀ E ∈ F, E.Nonempty → 2 ≤ E.card) :
    2 * (F.card - 1) ≤ ∑ E ∈ F, E.card := by
  classical
  let F' := F.erase ∅
  have hsum : 2 * F'.card ≤ ∑ E ∈ F', E.card := by
    calc
      2 * F'.card = ∑ E ∈ F', (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ E ∈ F', E.card := by
        apply Finset.sum_le_sum
        intro E hE
        exact hsize E ((Finset.erase_subset ∅ F) hE) (by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro hzero
          exact (Finset.mem_erase.mp hE).1 hzero)
  have hcard : F.card - 1 ≤ F'.card := by
    by_cases hmem : ∅ ∈ F
    · exact (Finset.card_erase_of_mem hmem).symm.le
    · have heq : F' = F := Finset.erase_eq_self.2 hmem
      rw [heq]
      omega
  have hsum' : ∑ E ∈ F', E.card ≤ ∑ E ∈ F, E.card := by
    by_cases hmem : ∅ ∈ F
    · have hs : (∑ E ∈ F.erase ∅, E.card) = ∑ E ∈ F, E.card :=
        Finset.sum_erase (s := F) (f := fun E : Finset X => E.card)
          (a := ∅) (by simp)
      simpa [F'] using hs.le
    · have heq : F' = F := Finset.erase_eq_self.2 hmem
      rw [heq]
  omega

end MathlibPlus.Combinatorics.Claim46620
