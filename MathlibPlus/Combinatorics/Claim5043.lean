import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim5043

/-- The shape-count decomposition from claim 5043.

A shape is represented by the isomorphism class of a finite simple graph with
no isolated vertex.  The cumulative count `g` is the sum of these classes over
all vertex counts at most its argument, so the displayed difference retains the
source's `h_n = g_n - g_(n-1)` conclusion without replacing shapes by labelled
graphs. -/
theorem shapeCount_difference_claim5043 (n : ℕ) (hn : 0 < n) :
    let h : ℕ → ℕ := fun m =>
      let α := {G : SimpleGraph (Fin m) // ∀ v, ∃ w, G.Adj v w}
      let s : Setoid α :=
        { r := fun G H => Nonempty (SimpleGraph.Iso G.1 H.1)
          iseqv :=
            { refl := fun G => ⟨SimpleGraph.Iso.refl⟩
              symm := fun {G H} hGH => ⟨hGH.some.symm⟩
              trans := fun {G H K} hGH hHK =>
                ⟨hHK.some.comp hGH.some⟩ } }
      Nat.card (Quotient s)
    let g : ℕ → ℕ := fun k => ∑ m ∈ Finset.range (k + 1), h m
    h n = g n - g (n - 1) := by
  classical
  dsimp
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  rw [hn', Finset.sum_range_succ]
  exact (Nat.add_sub_cancel_left _ _).symm

end MathlibPlus.Combinatorics.Claim5043
