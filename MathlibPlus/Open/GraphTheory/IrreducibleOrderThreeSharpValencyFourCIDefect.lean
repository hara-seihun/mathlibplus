import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- For every prime `p ≡ 2 (mod 3)`, `p ≠ 2`, the irreducible companion
order-three action on `𝔽_p²` gives a sharp valency-four ordinary Cayley CI
defect. -/
def irreducibleOrderThreeSharpValencyFourCIDefect : Prop :=
  ∀ p : ℕ,
    p.Prime →
    p % 3 = 2 →
    p ≠ 2 →
    let V := ZMod p × ZMod p
    let G := V × ZMod 3
    let A : V → V := fun v => (-v.2, v.1 - v.2)
    let act : ZMod 3 → V → V := fun k v => (A^[k.val]) v
    let mul : G → G → G := fun g h =>
      (g.1 + act g.2 h.1, g.2 + h.2)
    let rightDiff : G → G → G := fun g h =>
      (act (-g.2) (h.1 - g.1), h.2 - g.2)
    let inv : G → G := fun g => (-act (-g.2) g.1, -g.2)
    let one : G := ((0, 0), 0)
    let S : Set G :=
      {((1, 0), 0), ((-1, 0), 0), ((0, 1), 0), ((0, -1), 0)}
    let T : Set G :=
      {((2, 0), 0), ((-2, 0), 0), ((0, 1), 0), ((0, -1), 0)}
    S.ncard = 4 ∧
    T.ncard = 4 ∧
    one ∉ S ∧
    one ∉ T ∧
    (∀ g, g ∈ S ↔ inv g ∈ S) ∧
    (∀ g, g ∈ T ↔ inv g ∈ T) ∧
    (∃ q : G ≃ G,
      q one = one ∧
      ∀ x y : G, rightDiff x y ∈ S ↔ rightDiff (q x) (q y) ∈ T) ∧
    (¬ ∃ α : G ≃ G,
      α one = one ∧
      (∀ x y : G, α (mul x y) = mul (α x) (α y)) ∧
      α '' S = T) ∧
    ∀ U W : Set G,
      one ∉ U →
      one ∉ W →
      (∀ g, g ∈ U ↔ inv g ∈ U) →
      (∀ g, g ∈ W ↔ inv g ∈ W) →
      U.ncard < 4 →
      W.ncard < 4 →
      (∃ e : G ≃ G,
        ∀ x y : G, rightDiff x y ∈ U ↔ rightDiff (e x) (e y) ∈ W) →
      ∃ α : G ≃ G,
        α one = one ∧
        (∀ x y : G, α (mul x y) = mul (α x) (α y)) ∧
        α '' U = W

end MathlibPlus.Open.GraphTheory
