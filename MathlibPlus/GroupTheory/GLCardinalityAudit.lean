import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.GroupTheory

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The cardinality audit for `GL(2, 7)`: the standard finite-field formula
returns 2016, so the packet's value 48 cannot be the cardinality of the full
linear group. -/
theorem glTwoZModSevenCardinality_claim55412 :
    Nat.card (GL (Fin 2) (ZMod 7)) = (7 ^ 2 - 1) * (7 ^ 2 - 7) ∧
      Nat.card (GL (Fin 2) (ZMod 7)) = 2016 ∧
      Nat.card (GL (Fin 2) (ZMod 7)) ≠ 48 := by
  have hcard : Nat.card (GL (Fin 2) (ZMod 7)) =
      ∏ i : Fin 2, (Fintype.card (ZMod 7) ^ 2 - Fintype.card (ZMod 7) ^ (i : ℕ)) := by
    exact @Matrix.card_GL_field (ZMod 7) inferInstance inferInstance 2
  have hfield : Fintype.card (ZMod 7) = 7 := by
    simp
  rw [hcard, hfield]
  norm_num [Fin.prod_univ_two]

end MathlibPlus.GroupTheory
