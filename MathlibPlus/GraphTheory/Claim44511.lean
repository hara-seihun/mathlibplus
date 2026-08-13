import Mathlib

namespace MathlibPlus.GraphTheory.Claim44511

/-- The canonical `Fin n` relabeling of a vertex-deleted card is graph-isomorphic
    to the induced graph on the complement of the deleted vertex. -/
theorem deletedCard_succAbove_iso
    {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (deleted : Fin (n + 1)) :
    Nonempty (G.comap deleted.succAbove ≃g G.induce ({deleted}ᶜ : Set (Fin (n + 1)))) := by
  let e : Fin n ≃ {x : Fin (n + 1) // x ∈ ({deleted}ᶜ : Set (Fin (n + 1)))} :=
    Equiv.ofBijective
      (fun i => ⟨deleted.succAbove i, by simp⟩)
      (by
        constructor
        · intro i j hij
          exact deleted.succAbove_right_injective (congrArg Subtype.val hij)
        · intro x
          have hx : (x : Fin (n + 1)) ≠ deleted := by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
          obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hx
          refine ⟨i, ?_⟩
          apply Subtype.ext
          exact hi)
  exact ⟨SimpleGraph.Iso.comap e (G.induce ({deleted}ᶜ : Set (Fin (n + 1))))⟩

end MathlibPlus.GraphTheory.Claim44511
