import Mathlib

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

/-- Claim 29693: the exact q jump under one-leaf attachment is `d-1`,
with the degree-two case creating a trivalent branch. -/
def leafAttachmentBranchJump_claim29693 : Prop := by
  classical
  exact ∀ (V : Type) [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (T : SimpleGraph (Option V))
    (v : V) (d : ℕ),
    C.IsTree →
    C.degree v = d →
    2 ≤ d →
    (∀ x y : Option V,
      T.Adj x y ↔
        match x, y with
        | some a, some b => C.Adj a b
        | none, some a => a = v
        | some a, none => a = v
        | none, none => False) →
    T.IsTree ∧
      (∑ x : Option V, Nat.choose (T.degree x - 1) 2) -
          (∑ x : V, Nat.choose (C.degree x - 1) 2) = d - 1 ∧
      T.degree (some v) = d + 1 ∧
      (d = 2 → T.degree (some v) = 3) ∧
      (3 ≤ d → T.degree (some v) ≥ 4)

end MathlibPlus.Open.Combinatorics
