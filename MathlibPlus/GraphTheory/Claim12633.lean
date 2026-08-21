-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib.Data.Fin.Basic

namespace MathlibPlus.GraphTheory.Claim12633

/-- The four vertex-deleted cards of `P₄` have the twin pairs described in
claim 12633.  The local `cardAdj` relation makes the deleted vertex explicit,
so no identification of an induced-card subtype is hidden in the statement. -/
theorem deletedP4_twin_structure :
    let cardAdj := fun (d u v : Fin 4) =>
      u ≠ d ∧ v ≠ d ∧
        (u.val + 1 = v.val ∨ v.val + 1 = u.val)
    (1 ≠ (3 : Fin 4) ∧ 1 ≠ (0 : Fin 4) ∧ 3 ≠ (0 : Fin 4) ∧
        (cardAdj 0 1 1 ↔ cardAdj 0 3 1) ∧
        (cardAdj 0 1 2 ↔ cardAdj 0 3 2) ∧
        (cardAdj 0 1 3 ↔ cardAdj 0 3 3)) ∧
      (0 ≠ (2 : Fin 4) ∧ 0 ≠ (3 : Fin 4) ∧ 2 ≠ (3 : Fin 4) ∧
        (cardAdj 3 0 0 ↔ cardAdj 3 2 0) ∧
        (cardAdj 3 0 1 ↔ cardAdj 3 2 1) ∧
        (cardAdj 3 0 2 ↔ cardAdj 3 2 2)) ∧
      (2 ≠ (3 : Fin 4) ∧ 2 ≠ (1 : Fin 4) ∧ 3 ≠ (1 : Fin 4) ∧
        cardAdj 1 2 3 ∧ (cardAdj 1 2 0 ↔ cardAdj 1 3 0)) ∧
      (0 ≠ (1 : Fin 4) ∧ 0 ≠ (2 : Fin 4) ∧ 1 ≠ (2 : Fin 4) ∧
        cardAdj 2 0 1 ∧ (cardAdj 2 0 3 ↔ cardAdj 2 1 3)) := by
  dsimp
  constructor
  · native_decide
  constructor
  · native_decide
  constructor <;> native_decide

end MathlibPlus.GraphTheory.Claim12633
