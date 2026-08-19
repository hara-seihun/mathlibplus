import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 16485: the upstream strongly-regular predicate is exactly the
v-vertex, k-regular, simple-graph condition with λ common neighbors on every
adjacent pair and μ common neighbors on every distinct nonadjacent pair. -/
def stronglyRegularParameters_claim16485 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v k lam mu : ℕ),
    G.IsSRGWith v k lam mu ↔
      (Fintype.card V = v ∧
        G.IsRegularOfDegree k ∧
        (∀ x y, G.Adj x y →
          Fintype.card (G.commonNeighbors x y) = lam) ∧
        (∀ x y, x ≠ y → ¬ G.Adj x y →
          Fintype.card (G.commonNeighbors x y) = mu))

end MathlibPlus.Open.GraphTheory
