import Mathlib

namespace MathlibPlus.Combinatorics.Claim22625

/-- A symmetric `ZMod 2` signing of the edges of a complete graph with zero
triangle sums is an additive coboundary.  The signing is only constrained on
edges (`i ≠ j`), so no loop/diagonal hypothesis is added; the base coordinate is
set separately to zero. -/
theorem zeroTriangleParity_coboundary
    {V : Type*} [Nonempty V]
    (s : V → V → ZMod 2)
    (hsymm : ∀ i j, s i j = s j i)
    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
      s i j + s j k + s k i = 0)
    (q : V) :
    ∃ x : V → ZMod 2, x q = 0 ∧
      (∀ i, i ≠ q → x i = s q i) ∧
      ∀ i j, i ≠ j → s i j = x i + x j := by
  classical
  let x : V → ZMod 2 := fun i => if i = q then 0 else s q i
  have hxq : x q = 0 := by
    simp [x]
  refine ⟨x, hxq, ?_, ?_⟩
  · intro i hi
    simp [x, hi]
  · intro i j hij
    by_cases hiq : i = q
    · subst i
      have hjq : j ≠ q := Ne.symm hij
      simp [x, hij, hjq]
    · by_cases hjq : j = q
      · subst j
        simp [x, hiq, hsymm]
      · have h := htri q i j (Ne.symm hiq) hij hjq
        have h' : s q i + s i j + s q j = 0 := by
          simpa [hsymm j q] using h
        simp [x, hiq, hjq]
        calc
          s i j = -(s q i + s q j) := by linear_combination h'
          _ = s q i + s q j := by rw [ZMod.neg_eq_self_mod_two]

end MathlibPlus.Combinatorics.Claim22625
