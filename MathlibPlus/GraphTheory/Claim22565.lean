import Mathlib

namespace MathlibPlus.GraphTheory.Claim22565

/--
Two seven-vertex simple graphs with the displayed (unordered) degree sequences
cannot be isomorphic.  This is the degree-sequence argument behind admitted
claim 22565; no tree-specific property is needed once the sequences are fixed.
-/
theorem nonisomorphic_of_degree_sequences_claim22565
    (G H : SimpleGraph (Fin 7))
    (hG : ∃ e : Equiv.Perm (Fin 7),
      ∀ v, Nat.card (G.neighborSet (e v)) = ![4, 2, 2, 1, 1, 1, 1] v)
    (hH : ∃ e : Equiv.Perm (Fin 7),
      ∀ v, Nat.card (H.neighborSet (e v)) = ![3, 3, 2, 1, 1, 1, 1] v) :
    ¬ Nonempty (G ≃g H) := by
  rcases hG with ⟨eG, hG⟩
  rcases hH with ⟨eH, hH⟩
  rintro ⟨f⟩
  have hG4 : Nat.card (G.neighborSet (eG 0)) = 4 := by
    simpa using hG 0
  have hH4 : Nat.card (H.neighborSet (f (eG 0))) = 4 := by
    rw [← Nat.card_congr (f.mapNeighborSet (eG 0))]
    exact hG4
  rcases eH.surjective (f (eG 0)) with ⟨v, hv⟩
  rw [← hv, hH v] at hH4
  fin_cases v <;> norm_num at hH4

end MathlibPlus.GraphTheory.Claim22565
