import Mathlib

namespace MathlibPlus.Open.Combinatorics

private def positivePartialSums47174 {G : Type*} [AddMonoid G]
    (B : List G) : List G :=
  (List.scanl (fun s x => s + x) 0 B).tail

private def validOrdering47174 {G : Type*} [AddMonoid G]
    (B : List G) : Prop :=
  (positivePartialSums47174 B).Nodup

/-- Claim 47174: the two finite-field endpoint/same-position examples have
exactly the stated repeated and valid partial-sum lists. -/
def claim47174 : Prop :=
  let x7 : ZMod 7 := 1
  let y7 : ZMod 7 := 5
  let z7 : ZMod 7 := 6
  let B7 : List (ZMod 7) := [z7, 2, 4]
  let splitLeft7 : List (ZMod 7) := [x7, y7, 2, 4]
  let splitRight7 : List (ZMod 7) := [y7, x7, 2, 4]
  let reorderedB7 : List (ZMod 7) := [z7, 4, 2]
  let rearrangedSplit7 : List (ZMod 7) := [x7, y7, 4, 2]
  let a5 : ZMod 5 := 4
  let B5 : List (ZMod 5) := [2, 3, 1]
  let fullOrdering5 : List (ZMod 5) := [1, 2, a5, 3]
  x7 + y7 = z7 ∧
    positivePartialSums47174 B7 = [z7, 1, 5] ∧
    validOrdering47174 B7 ∧
    1 ∈ positivePartialSums47174 B7 ∧
    5 ∈ positivePartialSums47174 B7 ∧
    ¬ validOrdering47174 splitLeft7 ∧
    ¬ validOrdering47174 splitRight7 ∧
    reorderedB7.toFinset = B7.toFinset ∧
    positivePartialSums47174 reorderedB7 = [z7, 3, 5] ∧
    validOrdering47174 reorderedB7 ∧
    rearrangedSplit7.toFinset =
      B7.toFinset.erase z7 ∪ ({x7, y7} : Finset (ZMod 7)) ∧
    positivePartialSums47174 rearrangedSplit7 = [x7, 6, 3, 5] ∧
    validOrdering47174 rearrangedSplit7 ∧
    a5 ∉ B5 ∧
    positivePartialSums47174 B5 = [2, 0, 1] ∧
    validOrdering47174 B5 ∧
    B5.sum = (1 : ZMod 5) ∧
    (0 : ZMod 5) ∈ positivePartialSums47174 B5 ∧
    B5.sum + a5 = 0 ∧
    B5.sum + a5 ∈ positivePartialSums47174 B5 ∧
    ¬ validOrdering47174 (a5 :: B5) ∧
    ¬ validOrdering47174 (B5 ++ [a5]) ∧
    fullOrdering5.toFinset = B5.toFinset ∪ {a5} ∧
    positivePartialSums47174 fullOrdering5 = [1, 3, 2, 0] ∧
    validOrdering47174 fullOrdering5

end MathlibPlus.Open.Combinatorics
