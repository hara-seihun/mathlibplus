import MathlibPlus.Open.GraphTheory.Order105ComplementClaims

namespace MathlibPlus.Open.GraphTheory.Order105

/-- The group laws of the fixed semidirect-product coordinate model. -/
def g105GroupAxioms : Prop :=
  (∀ x : G105, g105Mul g105One x = x ∧ g105Mul x g105One = x) ∧
    (∀ x y z : G105,
      g105Mul (g105Mul x y) z = g105Mul x (g105Mul y z)) ∧
    (∀ x : G105,
      g105Mul x (g105Inv x) = g105One ∧
        g105Mul (g105Inv x) x = g105One)

/-- Claim 37518: the fixed order-105 group is the displayed
`C₃₅ ⋊₁₆ C₃` model, with the `C₃` generator acting on `C₃₅` by 16. -/
def claim37518_order105GroupModel : Prop :=
  Fintype.card G105 = 105 ∧
    g105GroupAxioms ∧
    (∀ i j : ZMod 3, ∀ n m : ZMod 35,
      g105Mul (i, n) (j, m) =
        (i + j, n + g105Action16 i * m)) ∧
    g105Action16 0 = 1 ∧
    g105Action16 1 = (16 : ZMod 35) ∧
    (∀ i : ZMod 3,
      g105Action16 i = (16 : ZMod 35) ^ i.val) ∧
    (∀ n : ZMod 35,
      g105Mul (1, 0) (0, n) = (1, (16 : ZMod 35) * n))

end MathlibPlus.Open.GraphTheory.Order105
