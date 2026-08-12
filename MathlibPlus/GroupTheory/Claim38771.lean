import Mathlib

namespace MathlibPlus.GroupTheory.Claim38771

/-- Aperiodicity makes the point action on the translate development faithful.
The membership equivalence in `hfix` is the setwise assertion that every
translate of `Y` is fixed by the permutation. -/
theorem translate_development_faithful
    {G : Type*} [AddCommGroup G]
    (Y : Set G)
    (haper : ∀ d : G, (∀ u : G, u + d ∈ Y ↔ u ∈ Y) → d = 0)
    (σ : Equiv.Perm G)
    (hfix : ∀ (t x : G), (x - t ∈ Y ↔ σ x - t ∈ Y)) :
    σ = 1 := by
  apply Equiv.Perm.ext
  intro x
  have hinv : ∀ u : G, u + (σ x - x) ∈ Y ↔ u ∈ Y := by
    intro u
    have h := hfix (x - u) x
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h.symm
  have hd : σ x - x = 0 := haper (σ x - x) hinv
  exact sub_eq_zero.mp hd

end MathlibPlus.GroupTheory.Claim38771
