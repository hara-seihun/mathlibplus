import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The complete nonzero-period sector of `C₄ × 𝔽₃³`, as an open claim. -/
def completeNonzeroPeriodSectorC4C3 : Prop :=
  let G := ZMod 4 × (Fin 3 → ZMod 3)
  let inverseClosed : Set G → Prop := fun R =>
    ∀ x, x ∈ R → -x ∈ R
  let period : Set G → Set G := fun R =>
    {g | (fun x : G => x + g) '' R = R}
  let cayleyAdj : Set G → G → G → Prop := fun R x y => y - x ∈ R
  let ci : Set G → Prop := fun R =>
    ∀ T : Set G,
      0 ∉ T →
      inverseClosed T →
      (∃ e : Equiv G G, ∀ x y,
        cayleyAdj R x y ↔ cayleyAdj T (e x) (e y)) →
      ∃ α : G ≃+ G, (fun x => α x) '' R = T
  ∀ S : Set G,
    S ⊆ (Set.univ : Set G) \ {0} →
    inverseClosed S →
    period S ≠ ({0} : Set G) →
    ci S ∧ ci (((Set.univ : Set G) \ {0}) \ S)

end MathlibPlus.Open.GraphTheory
