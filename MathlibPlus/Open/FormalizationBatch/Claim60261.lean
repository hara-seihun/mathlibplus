import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- The admitted six-involution CI statement for the two groups in the packet. -/
def claim60261 : Prop :=
  ∀ r : ℕ, (r = 4 ∨ r = 5) →
    let V := Fin r → ZMod 2
    let G := V × ZMod 9
    let inverseClosed : Set G → Prop := fun U =>
      ∀ g : G, g ∈ U → -g ∈ U
    let cayleyAdj : Set G → G → G → Prop := fun U x y =>
      x ≠ y ∧ ∃ s : G, s ∈ U ∧ x + s = y
    ∀ S : Set G,
      S.Finite ∧ Set.ncard S = 6 ∧
        (∀ s : G, s ∈ S → s.2 = 0) ∧
        (0, 0) ∉ S →
      inverseClosed S ∧
        (∀ T : Set G,
          (0, 0) ∉ T ∧ inverseClosed T →
            ((∃ f : G → G,
                Function.Bijective f ∧
                  ∀ x y : G,
                    cayleyAdj S x y ↔ cayleyAdj T (f x) (f y)) →
              ∃ α : G → G,
                Function.Bijective α ∧ α 0 = 0 ∧
                  (∀ x y : G, α (x + y) = α x + α y) ∧
                  α '' S = T))

end MathlibPlus.Open.FormalizationBatch
