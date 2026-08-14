import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

section LeafSuspension

variable {V : Type*} [Fintype V] [DecidableEq V]

def leafSuspensionGraph (G : SimpleGraph V) (r : V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel (fun x y =>
    match x, y with
    | some x, some y => G.Adj x y
    | none, some y => y = r
    | some x, none => x = r
    | none, none => False)

def rootedGraph (G : SimpleGraph V) (r : V) : SimpleGraph V × V :=
  (G, r)

def underlyingGraph (R : SimpleGraph V × V) : SimpleGraph V :=
  R.1

/-- Claim 48226: adjoining one explicit leaf produces one unrooted tree whose
new-leaf and old-root rootings differ only in the retained root. -/
def claim48226 : Prop :=
  ∀ (k : Nat),
    1 ≤ k →
      ∀ (_j : Fin k),
        ∀ {V : Type*} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) (r : V),
          G.IsTree →
            2 ≤ Fintype.card V →
              let Y := leafSuspensionGraph G r
              Y.IsTree ∧
                underlyingGraph (rootedGraph Y none) =
                  underlyingGraph (rootedGraph Y (some r))

end LeafSuspension

end MathlibPlus.Open.FormalizationBatch
