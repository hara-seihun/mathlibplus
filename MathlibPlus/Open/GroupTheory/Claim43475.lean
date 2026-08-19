import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim43475

/-- Claim 43475: the concrete scalar-two rank-four `C₇` cell has the stated
modular data, fixed-point-free scalar action, semidirect carrier, and order. -/
def claim43475 : Prop :=
  let M := Fin 4 → ZMod 7
  (7 % 3 = 1) ∧
    (2 ^ 3 % 7 = 1) ∧
    (Nat.gcd (2 * (2 - 1)) 7 = 1) ∧
    IsUnit (2 - 1 : ZMod 7) ∧
    (∀ v : M,
      (2 : ZMod 7) • v = v → v = 0) ∧
    (Fintype.card M = 7 ^ 4) ∧
    (Fintype.card (M × ZMod 3) = 7203) ∧
    (∃ action : ZMod 3 → M → M,
      (∀ k v w, action k (v + w) = action k v + action k w) ∧
        (∀ k, Function.Bijective (action k)) ∧
          (∀ k l v, action (k + l) v = action k (action l v)) ∧
            (∀ v, action 1 v = (2 : ZMod 7) • v))

end MathlibPlus.Open.GroupTheory.Claim43475
