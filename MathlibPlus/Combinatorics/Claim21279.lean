-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics.Claim21279

/--
The explicit six-bit endpoint from claim 21279, including the normalization
conditions recorded in claim 21280.  The join of two families is formed by
taking the bitwise OR of one member of each family.
-/
theorem explicitSharp18EndpointNormalized :
    let P : Finset (BitVec 6) := {31, 47, 55, 59, 61, 62, 63}
    let A : Finset (BitVec 6) :=
      {7, 11, 13, 14, 15, 23, 27, 30, 31, 39, 43, 45, 46, 47, 55, 59, 62, 63}
    let B : Finset (BitVec 6) :=
      {31, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63}
    let join : Finset (BitVec 6) → Finset (BitVec 6) → Finset (BitVec 6) :=
      fun X Y => (X.product Y).image (fun p => p.1 ||| p.2)
    let unionClosed : Finset (BitVec 6) → Prop :=
      fun X => ∀ a ∈ X, ∀ b ∈ X, a ||| b ∈ X
    let emptyFree : Finset (BitVec 6) → Prop := fun X => 0 ∉ X
    let emptyIntersection : Finset (BitVec 6) → Prop :=
      fun X => ∀ i : Fin 6, ∃ a ∈ X, a.getLsb i = false
    P.card = 7 ∧ A.card = 18 ∧ B.card = 18 ∧
      A.Nonempty ∧ B.Nonempty ∧
      unionClosed A ∧ unionClosed B ∧
      emptyFree A ∧ emptyFree B ∧
      emptyIntersection A ∧ emptyIntersection B ∧
      join A B = P := by
  native_decide

end MathlibPlus.Combinatorics.Claim21279
