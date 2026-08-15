import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

/-- The current cut out by a set of participating blocks. -/
def cutCurrent {𝕜 : Type*} [Field 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {J : Type*} [Fintype J] (v : J → V) (I : Finset J) : V :=
  I.sum v

/--
Every nonempty proper cut of a nontrivial pointed circuit has nonzero current.
A nontrivial pointed circuit is represented by its finite projected family: its
full sum vanishes, while each proper subfamily is linearly independent.
-/
def everyNontrivialCutCurrentIsNonzero
    (𝕜 : Type*) [Field 𝕜]
    (V : Type*) [AddCommGroup V] [Module 𝕜 V]
    (J : Type*) [Fintype J] [DecidableEq J]
    (v : J → V) : Prop :=
  2 ≤ Fintype.card J →
    (∑ b : J, v b = 0) →
      (∀ I : Finset J, I ⊂ Finset.univ →
        LinearIndependent 𝕜 (fun b : I => v b.1)) →
        ∀ I : Finset J, I.Nonempty → I ⊂ Finset.univ →
          cutCurrent (𝕜 := 𝕜) v I ≠ 0

end MathlibPlus.Open
