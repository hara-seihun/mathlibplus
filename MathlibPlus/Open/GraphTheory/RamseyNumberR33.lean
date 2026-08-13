import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The exact two-colouring formulation of the classical value `R(3,3) = 6`.
The red and blue graphs partition the edges of the complete graph; the first
conjunct is the universal order-six assertion and the second is the order-five
lower-bound witness assertion. -/
def ramseyNumber_R33_claim58970 : Prop :=
  (∀ (red blue : SimpleGraph (Fin 6)),
      red ⊔ blue = ⊤ →
      red ⊓ blue = ⊥ →
      (∃ s : Finset (Fin 6), red.IsNClique 3 s) ∨
        (∃ s : Finset (Fin 6), blue.IsNClique 3 s)) ∧
    ∃ (red blue : SimpleGraph (Fin 5)),
      red ⊔ blue = ⊤ ∧
      red ⊓ blue = ⊥ ∧
      (¬ ∃ s : Finset (Fin 5), red.IsNClique 3 s) ∧
      (¬ ∃ s : Finset (Fin 5), blue.IsNClique 3 s)

end MathlibPlus.Open.GraphTheory
