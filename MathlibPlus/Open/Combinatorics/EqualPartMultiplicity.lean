import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics

/-- Positive state labels `1, ..., m`, represented by the positive elements of `Fin (m + 1)`. -/
abbrev PositiveStateLabel (m : ℕ) := {s : Fin (m + 1) // 0 < s.val}

/-- The product of factorials of the multiplicities of the distinct parts of a list. -/
def equalPartMultiplicityFactor (parts : List ℕ) : ℕ :=
  (parts.eraseDups.map (fun a => (parts.count a).factorial)).prod

/-- A finite list is a partition when its positive parts are in weakly decreasing order. -/
def IsPartition (parts : List ℕ) : Prop :=
  List.Pairwise (fun a b => b ≤ a) parts ∧ ∀ a ∈ parts, 0 < a

/-- Assignments of pairwise distinct positive state labels to the components of `λ`. -/
abbrev DistinctStateAssignment (parts : List ℕ) (m : ℕ) :=
  {f : Fin parts.length → PositiveStateLabel m // Function.Injective f}

/-- The exponent of `x_s` in the monomial induced by an assignment. -/
def xExponent (parts : List ℕ) {m : ℕ}
    (f : Fin parts.length → PositiveStateLabel m)
    (s : PositiveStateLabel m) : ℕ :=
  ∑ j : Fin parts.length, if f j = s then parts.get j else 0

/-- The exponent of `z_s` in the monomial induced by an assignment. -/
def zExponent (parts : List ℕ) {m : ℕ}
    (f : Fin parts.length → PositiveStateLabel m)
    (s : PositiveStateLabel m) : ℕ :=
  ∑ j : Fin parts.length, if f j = s then parts.get j - 1 else 0

/-- The `y`, `x`, and `z` exponent data of the monomial induced by an assignment. -/
def componentMonomial (parts : List ℕ) {m : ℕ}
    (f : DistinctStateAssignment parts m) :=
  (parts.length - 1,
    fun s => xExponent parts f.1 s,
    fun s => zExponent parts f.1 s)

/-- Two assignments yield the same component monomial. -/
def sameComponentMonomial (parts : List ℕ) {m : ℕ}
    (f g : DistinctStateAssignment parts m) : Prop :=
  componentMonomial parts f = componentMonomial parts g

/--
Equal-part multiplicity factor: for a partition `λ`, the product of factorials of
part multiplicities is exactly the number of pairwise-distinct positive-state
assignments yielding the same monomial under permutations of equal component
sizes.
-/
def equalPartMultiplicityFactor_claim : Prop :=
  ∀ (m : ℕ) (parts : List ℕ),
    0 < m →
    IsPartition parts →
    parts.length ≤ m →
    ∀ f : DistinctStateAssignment parts m,
      Nat.card {g : DistinctStateAssignment parts m // sameComponentMonomial parts f g} =
        equalPartMultiplicityFactor parts

end MathlibPlus.Open.Combinatorics
