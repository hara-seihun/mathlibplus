import Mathlib

namespace MathlibPlus.Open.Combinatorics


def hasCliqueFive {α : Type} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ s : Finset α,
    s.card = 5 ∧
    ∀ ⦃x y : α⦄, x ∈ s → y ∈ s → x ≠ y → G.Adj x y

def hasIndependentFive {α : Type} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ s : Finset α,
    s.card = 5 ∧
    ∀ ⦃x y : α⦄, x ∈ s → y ∈ s → x ≠ y → ¬ G.Adj x y

def goodFiveFive {α : Type} [Fintype α] (G : SimpleGraph α) : Prop :=
  ¬ hasCliqueFive G ∧ ¬ hasIndependentFive G

def ramsey55Threshold (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), hasCliqueFive G ∨ hasIndependentFive G

def leastRamsey55 (r : ℕ) : Prop :=
  ramsey55Threshold r ∧ ∀ n < r, ¬ ramsey55Threshold n

def diagonalRamseyNumberR55 : Prop :=
  ∃ r : ℕ,
    leastRamsey55 r ∧
    (∀ n : ℕ, n < r ↔ ∃ G : SimpleGraph (Fin n), goodFiveFive G)

def fortyTwoVertexGoodGraph : Prop :=
  (∃ G : SimpleGraph (Fin 42), goodFiveFive G) ∧
  (∀ r : ℕ, leastRamsey55 r → 43 ≤ r)

def refutedR55Equals50 : Prop :=
  ∃ r : ℕ, leastRamsey55 r ∧ r ≤ 46 ∧ r ≠ 50

end MathlibPlus.Open.Combinatorics
