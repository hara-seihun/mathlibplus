import Mathlib
import MathlibPlus.GraphTheory.Claim21230

namespace MathlibPlus.Open.ResearchFormalization.BatchR0427Claim21231

private def componentUnionGraph {V : Type*}
    (C : SimpleGraph V) (A : Set V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => C.Adj u v ∧ u ∈ A ∧ v ∈ A)

/-- Claim 21231: the two proper component unions from the exact component
partition, viewed on the common full vertex set, each expose an isolated
vertex on the opposite nonempty side. -/
def claim21231_properComponentUnionsHaveIsolates : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V),
    (∀ v, ¬ C.IsIsolated v) →
    (∃ c d : C.ConnectedComponent, c ≠ d) →
    ∃ A B : Set V,
      A.Nonempty ∧
        B.Nonempty ∧
        Disjoint A B ∧
        A ∪ B = Set.univ ∧
        (∀ ⦃u v : V⦄, C.Adj u v →
          (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) ∧
        (∃ v, v ∈ B ∧
          (componentUnionGraph C A).IsIsolated v) ∧
        (∃ v, v ∈ A ∧
          (componentUnionGraph C B).IsIsolated v)

end MathlibPlus.Open.ResearchFormalization.BatchR0427Claim21231
