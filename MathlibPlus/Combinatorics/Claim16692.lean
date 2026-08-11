import Mathlib

namespace MathlibPlus.Combinatorics

noncomputable section

/-- Claim 16692: the cochromatic number of a finite simple graph, encoded by
surjective colorings; every color class is required to be a clique or an
independent set. -/
def cochromaticNumber_claim16692 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ |
    ∃ c : V → Fin k, Function.Surjective c ∧
      ∀ i : Fin k,
        (∀ x y : V, c x = i → c y = i → x ≠ y → G.Adj x y) ∨
        (∀ x y : V, c x = i → c y = i → ¬ G.Adj x y)}

end

end MathlibPlus.Combinatorics
