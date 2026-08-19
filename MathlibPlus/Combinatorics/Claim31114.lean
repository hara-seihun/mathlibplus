import Mathlib

namespace MathlibPlus.Combinatorics.Claim31114

/--
Equality of cyclic first differences of two eight-coordinate words forces
 their pointwise difference to be constant.
-/
def firstDifference_eq_implies_constant_claim31114 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (c Γ : Fin 8 → ZMod p),
      (∀ i : Fin 8,
        c ⟨(i.val + 1) % 8, by omega⟩ - c i =
          Γ ⟨(i.val + 1) % 8, by omega⟩ - Γ i) →
      ∃ k : ZMod p, ∀ i : Fin 8, c i - Γ i = k

end MathlibPlus.Combinatorics.Claim31114
