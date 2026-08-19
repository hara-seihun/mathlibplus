import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 12659: a labelled undirected 43-circulant is determined by its
connection mask on the 21 nonzero unoriented distance classes, and the number
of such graphs is the resulting Boolean-mask count. -/
def circulantGraphCount_claim12659 : Prop :=
  let isCirculant : SimpleGraph (ZMod 43) → Prop := fun G =>
    ∀ x y : ZMod 43, G.Adj (x + 1) (y + 1) ↔ G.Adj x y
  let hasConnectionMask : SimpleGraph (ZMod 43) → Finset (Fin 21) → Prop :=
    fun G S =>
      ∀ x y : ZMod 43,
        G.Adj x y ↔
          ∃ d : Fin 21,
            d ∈ S ∧
              (x - y = ((d.val + 1 : ℕ) : ZMod 43) ∨
                x - y = -((d.val + 1 : ℕ) : ZMod 43))
  (∀ G : SimpleGraph (ZMod 43), isCirculant G →
      ∃! S : Finset (Fin 21), hasConnectionMask G S) ∧
    Nat.card {G : SimpleGraph (ZMod 43) // isCirculant G} = 2 ^ 21 ∧
    (2 ^ 21 : ℕ) = 2_097_152

end MathlibPlus.Open.GraphTheory
