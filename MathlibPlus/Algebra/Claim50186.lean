import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 50186: an explicit additive-integer prefix sequence reaches `-3`, while
its displayed splice value returns to the initial prefix vertex.  The finite
list and `List.take`/`List.sum` retain the actual prefix construction rather
than recording only a closed arithmetic receipt.
-/
theorem claim50186_explicitIntegerSpliceWitness :
    let B : List ℤ := [10, -11, 21, -22, 32, -33]
    let pref : ℕ → ℤ := fun i => (B.take i).sum
    let u : ℤ := 1
    let v : ℤ := 2
    let T : ℤ := pref 6
    let P₂ : ℤ := pref 2
    let P₄ : ℤ := pref 4
    let splice : ℤ := 2 * u - v
    pref 0 = 0 ∧
      pref 1 = 10 ∧
      pref 2 = -1 ∧
      pref 3 = 20 ∧
      pref 4 = -2 ∧
      pref 5 = 30 ∧
      T = -3 ∧
      P₂ = -u ∧
      P₄ = -v ∧
      splice = pref 0 := by
  norm_num [List.take, List.sum_cons]

end MathlibPlus.Algebra
