import Mathlib

namespace MathlibPlus.Open.GraphTheory

open scoped Classical BigOperators

noncomputable section

def vertexCard {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph {w : Fin n // w ≠ v} :=
  G.induce {w : Fin n | w ≠ v}

def cardMultiplicityRow {n : ℕ} (G : SimpleGraph (Fin n))
    (K : SimpleGraph (Fin (n - 1))) : ℕ :=
  Fintype.card {v : Fin n // Nonempty (vertexCard G v ≃g K)}

def equalMultiplicityDeck {n : ℕ}
    (G H : SimpleGraph (Fin n)) : Prop :=
  ∀ K : SimpleGraph (Fin (n - 1)),
    cardMultiplicityRow G K = cardMultiplicityRow H K

def deckTwinFunctional {n : ℕ} (G H : SimpleGraph (Fin n))
    (f : SimpleGraph (Fin n) → ℤ) : ℤ :=
  f G - f H

def cardRowFunctional {n : ℕ} (K : SimpleGraph (Fin (n - 1)))
    (G : SimpleGraph (Fin n)) : ℤ :=
  cardMultiplicityRow G K

def linearCardRowPolynomial {n : ℕ}
    (c : SimpleGraph (Fin (n - 1)) → ℤ)
    (G : SimpleGraph (Fin n)) : ℤ :=
  ∑ K, c K * cardRowFunctional K G

def fallingQuadraticCardRowPolynomial {n : ℕ}
    (c : SimpleGraph (Fin (n - 1)) → SimpleGraph (Fin (n - 1)) → ℤ)
    (G : SimpleGraph (Fin n)) : ℤ :=
  ∑ K, ∑ L,
    c K L * cardRowFunctional K G *
      (cardRowFunctional L G - if K = L then 1 else 0)

/-- Claim 46645: equal multiplicity-weighted vertex decks annihilate each card
row and every linear and falling-quadratic polynomial in those rows. -/
def claim46645 : Prop :=
  ∀ (n : ℕ), 5 ≤ n →
    ∀ G H : SimpleGraph (Fin n), equalMultiplicityDeck G H →
      (∀ K : SimpleGraph (Fin (n - 1)),
        deckTwinFunctional G H (cardRowFunctional K) = 0) ∧
        (∀ c : SimpleGraph (Fin (n - 1)) → ℤ,
          linearCardRowPolynomial c G = linearCardRowPolynomial c H) ∧
          (∀ c : SimpleGraph (Fin (n - 1)) →
              SimpleGraph (Fin (n - 1)) → ℤ,
            fallingQuadraticCardRowPolynomial c G =
              fallingQuadraticCardRowPolynomial c H)

end

end MathlibPlus.Open.GraphTheory
