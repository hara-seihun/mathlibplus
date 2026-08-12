import Mathlib.Tactic

namespace MathlibPlus.Algebra

/--
Claim 52316 (R-4516#1): the order-five companion action on `F₃⁴`.
-/
def claim52316_companionAction (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![v 1, v 2, v 3, -v 0 - v 1 - v 2 - v 3]

/-- The displayed companion action has order dividing five, hence supplies
an action of the additive cyclic group of order five.
-/
theorem claim52316_companionAction_pow_five :
    ∀ v, claim52316_companionAction
      (claim52316_companionAction
        (claim52316_companionAction
          (claim52316_companionAction
            (claim52316_companionAction v)))) = v := by
  intro v
  funext i
  fin_cases i <;> simp [claim52316_companionAction] <;> abel

end MathlibPlus.Algebra
