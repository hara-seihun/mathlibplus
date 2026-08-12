import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

namespace MathlibPlus.Algebra.CrossFamilyTranslation

/--
The translation/permutation cross-family identity from claim 38500.
The first conjunct expands the local cross family, and the second is the
normalization identity for its translation parameters.
-/
theorem translation_difference
    {B : Type*} [AddCommGroup B] (q : Equiv.Perm B) (s t : B) :
    (∀ x : B,
      ((x + t) + s - q t) = x + (t + s - q t)) ∧
      ((t + s - q t) - (0 + s - q 0) = t - q t + q 0) := by
  constructor
  · intro x
    abel
  · abel

end MathlibPlus.Algebra.CrossFamilyTranslation
