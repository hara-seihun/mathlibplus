import Mathlib

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

/-- Claim 29692: on subcubic trees the `P₃` excess is exactly the number
of trivalent vertices, and the all-tree q-filtration restricts to that
branch-count grading. -/
def subcubicBranchStabilization_claim29692 : Prop := by
  classical
  exact ∀ (V : Type) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V),
    T.IsTree →
    (∀ v : V, T.degree v ≤ 3) →
    (∑ v : V, Nat.choose (T.degree v - 1) 2) =
      (Finset.univ.filter (fun v : V => T.degree v = 3)).card ∧
    ∀ (k : ℕ),
      {G : SimpleGraph V |
        G.IsTree ∧ (∀ v : V, G.degree v ≤ 3) ∧
          (∑ v : V, Nat.choose (G.degree v - 1) 2) ≤ k} =
      {G : SimpleGraph V |
        G.IsTree ∧ (∀ v : V, G.degree v ≤ 3) ∧
          (Finset.univ.filter (fun v : V => G.degree v = 3)).card ≤ k}

end MathlibPlus.Open.Combinatorics
