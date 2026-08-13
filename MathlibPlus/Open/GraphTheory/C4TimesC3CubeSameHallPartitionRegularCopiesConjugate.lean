import Mathlib

namespace MathlibPlus.Open.GraphTheory

/--
For `G = C₄ × C₃³`, two regular copies preserving the same ordinary
inverse-closed Cayley graph and having the same orbit partition under the
characteristic subgroup `2C₄` are conjugate by a graph automorphism.

The regular copies are represented explicitly by permutation actions `ρ` and
`τ`.  Equality of their two-point orbit relations states exactly that their
`2C₄`-orbit partitions agree.  The conclusion is equality of the two regular
permutation subgroups after conjugation, not merely conjugacy in an abstract
quotient automorphism group.
-/
def c4TimesC3CubeSameHallPartitionRegularCopiesConjugate : Prop :=
  let G := ZMod 4 × (Fin 3 → ZMod 3)
  let M := Multiplicative G
  let n : M := .ofAdd ((2 : ZMod 4), 0)
  ∀ (S : Set G),
    0 ∉ S →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    ∀ (ρ τ : M →* Equiv.Perm G),
      (∀ x y : G, ∃! a : M, ρ a x = y) →
      (∀ x y : G, ∃! a : M, τ a x = y) →
      (∀ a : M, ∀ x y : G,
        y - x ∈ S ↔ ρ a y - ρ a x ∈ S) →
      (∀ a : M, ∀ x y : G,
        y - x ∈ S ↔ τ a y - τ a x ∈ S) →
      (∀ x y : G,
        (y = x ∨ y = ρ n x) ↔ (y = x ∨ y = τ n x)) →
      ∃ g : Equiv.Perm G,
        (∀ x y : G, y - x ∈ S ↔ g y - g x ∈ S) ∧
          ∀ p : Equiv.Perm G,
            (∃ a : M, τ a = p) ↔
              ∃ a : M, g⁻¹ * ρ a * g = p

end MathlibPlus.Open.GraphTheory
