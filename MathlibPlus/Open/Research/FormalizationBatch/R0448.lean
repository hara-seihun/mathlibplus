import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- An edge of K_n, represented by its two-element endpoint set. -/
abbrev KEdge (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

abbrev EdgeSet (n : ℕ) := Finset (KEdge n)

/-- The Walsh character of an edge subset. -/
def walshCharacter {n : ℕ} (A X : EdgeSet n) : ℤ :=
  (-1 : ℤ) ^ (A.filter (fun e => e ∈ X)).card

/-- The fixed-wedge second difference on the face where the wedge is absent. -/
def fixedWedgeDifference {n : ℕ} (Φ : EdgeSet n → ℤ)
    (e f : KEdge n) (Y : EdgeSet n) : ℤ :=
  Φ Y - Φ (insert e Y) - Φ (insert f Y) +
    Φ (insert e (insert f Y))

def edgeAdjacent {n : ℕ} (e f : KEdge n) : Prop :=
  e ≠ f ∧ ∃ v : Fin n, v ∈ e.1 ∧ v ∈ f.1

/-- Exact second difference of a Walsh character at a fixed wedge. -/
def exactFixedWedgeSecondDifferenceFormula : Prop :=
  ∀ {n : ℕ} (A : EdgeSet n) (e f : KEdge n) (Y : EdgeSet n),
    edgeAdjacent e f →
    e ∉ Y →
    f ∉ Y →
      ((e ∈ A ∧ f ∈ A →
          fixedWedgeDifference (walshCharacter A) e f Y =
            4 * walshCharacter ((A.erase e).erase f) Y) ∧
        (e ∉ A ∨ f ∉ A →
          fixedWedgeDifference (walshCharacter A) e f Y = 0))

end MathlibPlus.Open.ResearchFormalizationBatch
