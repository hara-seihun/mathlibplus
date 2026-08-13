import Mathlib

namespace MathlibPlus.Open.Combinatorics

/--
Claim 16633.  A Boolean function is represented by a decision tree of depth at
most two: the root query may be absent, the second query may be absent or may
depend on the root answer, and no second query repeats the root coordinate.
Terminal output depends only on the answers that were actually queried.
-/
def depthTwoBooleanDecisionTree_claim16633 {ι : Type*}
    (f : (ι → Bool) → Bool) : Prop :=
  ∃ (root : Option ι) (second : Bool → Option ι)
      (terminal : Option Bool → Option Bool → Bool),
    (∀ b j, second b = some j → root ≠ some j) ∧
      ∀ x,
        match root with
        | none => f x = terminal none none
        | some r =>
            match second (x r) with
            | none => f x = terminal (some (x r)) none
            | some j => f x = terminal (some (x r)) (some (x j))

end MathlibPlus.Open.Combinatorics
