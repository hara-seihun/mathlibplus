import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

noncomputable def branchComponentOrder {V : Type*} [Fintype V]
    (T : SimpleGraph V) (c : V) (v : {w : V // w ≠ c}) : ℕ :=
  Set.ncard {w : {u : V // u ≠ c} |
    (T.induce {u : V | u ≠ c}).Reachable v w}

noncomputable def C9 {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Prop :=
  T.IsTree ∧ ∃ c : V, ∀ v : {w : V // w ≠ c},
    branchComponentOrder T c v ≤ 9

end ResearchFormalization
end Open
end MathlibPlus
