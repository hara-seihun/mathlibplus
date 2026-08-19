import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim54577Batch

private def subsetSum (S : Finset (ZMod 9)) : ZMod 9 → ℕ :=
  fun x => if x ∈ S then 1 else 0

private def convolution (f g : ZMod 9 → ℕ) : ZMod 9 → ℕ :=
  fun x => ∑ a : ZMod 9, f a * g (x - a)

/-- Claim 54577: the three displayed subset sums in the natural-number group
ring of C9 satisfy the exact convolution identities. -/
def claim54577_groupRingIdentitiesC9 : Prop :=
  let N0 : Finset (ZMod 9) := {0, 3, 6}
  let U9 : Finset (ZMod 9) := {1, 2, 4, 5, 7, 8}
  convolution (subsetSum U9) (subsetSum U9) =
      (fun x => 6 * subsetSum N0 x + 3 * subsetSum U9 x) ∧
    convolution (subsetSum N0) (subsetSum U9) =
      (fun x => 3 * subsetSum U9 x) ∧
    convolution (subsetSum N0) (subsetSum N0) =
      (fun x => 3 * subsetSum N0 x)

end MathlibPlus.Algebra.Claim54577Batch
