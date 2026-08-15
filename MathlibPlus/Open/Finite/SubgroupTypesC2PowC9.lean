import Mathlib

namespace MathlibPlus.Open

/-- Claim 28560: the subgroup types, orders, indices, and ten proper nontrivial
coset-action types of C₂³ × C₉. -/
def subgroupTypesOfC2CubedTimesC9 : Prop :=
  let G := (Fin 3 → ZMod 2) × ZMod 9
  let c9Subgroup :=
    fun b : ℕ => AddSubgroup.zmultiples (3 ^ (2 - b) : ZMod 9)
  (∀ H : AddSubgroup G,
    ∃ (a b : ℕ) (U : Submodule (ZMod 2) (Fin 3 → ZMod 2)),
      0 ≤ a ∧ a ≤ 3 ∧
        0 ≤ b ∧ b ≤ 2 ∧
        Module.finrank (ZMod 2) U = a ∧
        (∀ z : G,
          z ∈ H ↔ z.1 ∈ U ∧ z.2 ∈ c9Subgroup b) ∧
        Nat.card H = 2 ^ a * 3 ^ b ∧
        Fintype.card G / Nat.card H =
          2 ^ (3 - a) * 3 ^ (2 - b)) ∧
    Set.ncard
        {p : ℕ × ℕ |
          ∃ H : AddSubgroup G,
            H ≠ ⊥ ∧ H ≠ ⊤ ∧
              p = (Nat.card H, Fintype.card G / Nat.card H)} = 10

end MathlibPlus.Open
