import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim5539Formalization

variable {K R C : Type*} [Field K] [Fintype R] [Fintype C]

/-- The columns occurring with a nonzero entry in a row. -/
def rowSupport (A : Matrix R C K) (r : R) : Set C :=
  {c | A r c ≠ 0}

/-- The columns removed by singleton peeling through wave `k`. -/
def singletonPeelingWave (A : Matrix R C K) : ℕ → Set C
  | 0 => ∅
  | k + 1 =>
      singletonPeelingWave A k ∪
        {c | ∃ r, A r c ≠ 0 ∧
          ∀ d, d ≠ c → A r d ≠ 0 → d ∈ singletonPeelingWave A k}

/-- Every column is removed by the singleton-peeling process. -/
def completeSingletonPeeling (A : Matrix R C K) : Prop :=
  ∃ k, singletonPeelingWave A k = Set.univ

/-- A choice of one incident row for each column. -/
def incidentRowSelector (A : Matrix R C K) (s : C → R) : Prop :=
  ∀ c, A (s c) c ≠ 0

/-- The dependency arrows induced by an incident-row selector. -/
def dependencyArrow (A : Matrix R C K) (s : C → R) (c d : C) : Prop :=
  d ∈ rowSupport A (s c) \ {c}

/-- The selector dependency digraph has no directed cycle. -/
def dependencyAcyclic (A : Matrix R C K) (s : C → R) : Prop :=
  ∀ c, ¬Relation.TransGen (dependencyArrow A s) c c

/-- Complete singleton peeling is equivalent to the existence of an acyclic incident-row selector. -/
def completePeeling_iff_acyclicSelector (A : Matrix R C K) : Prop :=
  completeSingletonPeeling A ↔
    ∃ s : C → R, incidentRowSelector A s ∧ dependencyAcyclic A s

end MathlibPlus.Open.Combinatorics.Claim5539Formalization
