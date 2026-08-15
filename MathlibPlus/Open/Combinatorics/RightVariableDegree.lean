import Mathlib

namespace MathlibPlus.Open.Combinatorics

/--
For the bipartite edge-constraint multigraph associated to pointed local
permutations, every right edge-variable has one incoming constraint for each
deleted vertex outside that edge, and hence multidegree `n - 2`.
-/
def rightVariablesHaveDegreeNSubTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (π : V → Equiv.Perm V) : Prop :=
  Fintype.card V = n →
    (∀ i : V, π i i = i) →
    (∀ i : V,
      Set.BijOn
        (fun e : Finset V => e.image (π i))
        {e : Finset V | e.card = 2 ∧ i ∉ e}
        {e : Finset V | e.card = 2 ∧ i ∉ e}) →
    ∀ f : Finset V, f.card = 2 →
      (∀ i : V, i ∉ f →
        ∃! e : Finset V,
          e.card = 2 ∧ i ∉ e ∧ e.image (π i) = f) ∧
      Fintype.card
          {constraint : V × Finset V //
            constraint.1 ∉ constraint.2 ∧
            constraint.2.card = 2 ∧
            constraint.2.image (π constraint.1) = f} = n - 2

end MathlibPlus.Open.Combinatorics
