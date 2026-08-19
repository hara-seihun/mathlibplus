import Mathlib

namespace MathlibPlus.Combinatorics.Claim22203

/--
A double spider is represented by sorted positive pendant-leg lists at its two
branching endpoints and the length of the joining path.
-/
structure DoubleSpider where
  left : List ℕ
  join : ℕ
  right : List ℕ
  left_sorted : List.Pairwise (· ≤ ·) left
  right_sorted : List.Pairwise (· ≤ ·) right
  left_positive : ∀ n ∈ left, 0 < n
  right_positive : ∀ n ∈ right, 0 < n
  left_branching : 2 ≤ left.length
  right_branching : 2 ≤ right.length

/-- Exchange the two endpoints while retaining the joining path. -/
def endpointSwap (s : DoubleSpider) : DoubleSpider :=
  { left := s.right
    join := s.join
    right := s.left
    left_sorted := s.right_sorted
    right_sorted := s.left_sorted
    left_positive := s.right_positive
    right_positive := s.left_positive
    left_branching := s.right_branching
    right_branching := s.left_branching }

/-- Canonicalization identifies a representation with itself or its endpoint
swap. -/
def endpointEquivalent (s t : DoubleSpider) : Prop :=
  t = s ∨ t = endpointSwap s

end MathlibPlus.Combinatorics.Claim22203
