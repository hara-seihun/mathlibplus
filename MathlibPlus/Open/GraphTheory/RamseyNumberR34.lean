import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The exact two-colouring formulation of the classical value `R(3,4) = 9`.
The red and blue graphs partition the edges of the complete graph; the first
conjunct is the universal order-nine assertion and the second is the order-eight
lower-bound witness assertion. -/
def ramseyNumber_R34_claim58971 : Prop :=
  (∀ (red blue : SimpleGraph (Fin 9)),
      red ⊔ blue = ⊤ →
      red ⊓ blue = ⊥ →
      (∃ s : Finset (Fin 9), red.IsNClique 3 s) ∨
        (∃ s : Finset (Fin 9), blue.IsNClique 4 s)) ∧
    ∃ (red blue : SimpleGraph (Fin 8)),
      red ⊔ blue = ⊤ ∧
      red ⊓ blue = ⊥ ∧
      (¬ ∃ s : Finset (Fin 8), red.IsNClique 3 s) ∧
      (¬ ∃ s : Finset (Fin 8), blue.IsNClique 4 s)

end MathlibPlus.Open.GraphTheory
