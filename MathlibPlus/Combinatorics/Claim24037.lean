import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Registry node for the complete cover classification.  `addFree` and
`deleteMinimalTrace` are the source's two legal-operation predicates: their
internal cylinder, retained-top, minimal-trace, and nonempty-upset carriers
are deliberately supplied by the eventual faithful model rather than
silently reconstructed here. -/
def completeCoverClassification_claim24037
    (State : Type*) [PartialOrder State]
    (addFree deleteMinimalTrace : State → State → Prop) : Prop :=
  ∀ x y : State,
    (x < y ∧ ¬ ∃ z : State, x < z ∧ z < y) ↔
      addFree x y ∨ deleteMinimalTrace x y

end MathlibPlus.Open.Combinatorics
