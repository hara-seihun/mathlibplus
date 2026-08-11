import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics

/-- The regular-union core of admitted claim 36774: pairwise-disjoint
regular layers merge with per-member deleted rank equal to the sum of the
layer ranks, and with coordinate-incidence bound equal to the maximum layer
bound. -/
theorem simultaneousRegularLayers
    {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    {d : ℕ} (A : ι → Finset α) (Y : Fin d → Finset α)
    (p s : Fin d → ℕ) (S : ℕ)
    (hdisj : ∀ j k : Fin d, j ≠ k → Disjoint (Y j) (Y k))
    (hreg : ∀ i j, (A i ∩ Y j).card = p j)
    (hmax : (∀ j, s j ≤ S) ∧ ∃ j, s j = S)
    (hdeg : ∀ j x, x ∈ Y j →
      (Finset.univ.filter (fun i : ι => x ∈ A i)).card ≤ s j) :
    let Yall := Finset.univ.biUnion Y
    (∀ i, (A i ∩ Yall).card = ∑ j, p j) ∧
      (∀ x, x ∈ Yall →
        (Finset.univ.filter (fun i : ι => x ∈ A i)).card ≤ S) := by
  dsimp
  constructor
  · intro i
    rw [Finset.inter_biUnion]
    have hI :
        (↑(Finset.univ : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint
          (fun j => A i ∩ Y j) := by
      intro j hj k hk hne
      refine Finset.disjoint_left.2 ?_
      intro x hxj hxk
      exact (Finset.disjoint_left.1 (hdisj j k hne))
        (Finset.mem_inter.1 hxj).2 (Finset.mem_inter.1 hxk).2
    rw [Finset.card_biUnion hI]
    simp [hreg]
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨j, -, hxj⟩ := hx
    exact le_trans (hdeg j x hxj) (hmax.1 j)

end MathlibPlus.Combinatorics
