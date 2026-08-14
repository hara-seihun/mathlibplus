import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The ordered component-degree signature of a vertex. -/
noncomputable def componentDegreeSignature {V : Type*} [Fintype V] {k : Nat}
    (C : Fin k → SimpleGraph V) (v : V) : Fin k → Nat :=
  fun i => Nat.card ((C i).neighborSet v)

end MathlibPlus.Open.Combinatorics
