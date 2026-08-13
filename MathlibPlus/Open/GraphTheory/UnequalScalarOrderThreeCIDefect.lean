import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every unequal-eigenvalue fixed-point-free order-three diagonal action has
an ordinary Cayley CI defect of valency two. -/
def unequalScalarOrderThreeValencyTwoCIDefect : Prop :=
  ∀ (p : ℕ) (ω : ZMod p),
    p.Prime →
    ω ^ 3 = 1 →
    ω ≠ 1 →
    let V := ZMod p × ZMod p
    let G := V × ZMod 3
    let act : ZMod 3 → V → V := fun k v =>
      ((ω ^ k.val) * v.1, ((ω ^ 2) ^ k.val) * v.2)
    let mul : G → G → G := fun g h =>
      (g.1 + act g.2 h.1, g.2 + h.2)
    let rightDiff : G → G → G := fun g h =>
      (act (-g.2) (h.1 - g.1), h.2 - g.2)
    let inv : G → G := fun g => (-act (-g.2) g.1, -g.2)
    let one : G := ((0, 0), 0)
    let S : Set G := {((1, 0), 0), ((-1, 0), 0)}
    let T : Set G := {((1, 1), 0), ((-1, -1), 0)}
    S.ncard = 2 ∧
    T.ncard = 2 ∧
    one ∉ S ∧
    one ∉ T ∧
    (∀ g, g ∈ S ↔ inv g ∈ S) ∧
    (∀ g, g ∈ T ↔ inv g ∈ T) ∧
    (∃ q : G ≃ G,
      q one = one ∧
      ∀ x y : G, rightDiff x y ∈ S ↔ rightDiff (q x) (q y) ∈ T) ∧
    ¬ ∃ α : G ≃ G,
      α one = one ∧
      (∀ x y : G, α (mul x y) = mul (α x) (α y)) ∧
      α '' S = T

end MathlibPlus.Open.GraphTheory
