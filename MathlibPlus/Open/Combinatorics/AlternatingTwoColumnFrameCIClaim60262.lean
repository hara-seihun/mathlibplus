import Mathlib

namespace MathlibPlus.Open

/-- Isomorphism of the ordinary undirected Cayley graphs on an additive group. -/
def ordinaryUndirectedCayleyGraphIso_claim60262
    {V : Type*} [AddGroup V] (S T : Set V) : Prop :=
  ∃ f : V → V,
    Function.Bijective f ∧
      ∀ x y : V, (y - x ∈ S ↔ f y - f x ∈ T)

/-- The alternating two-column frame CI theorem. -/
def alternatingTwoColumnFrameCI_claim60262 : Prop :=
  ∀ (p r : ℕ) (hp5 : 5 ≤ p) (hp : Nat.Prime p) (hr : 6 ≤ r),
    letI : Fact p.Prime := ⟨hp⟩
    let V := Fin r → ZMod p
    let e : Fin r → V := fun i => Pi.single i (1 : ZMod p)
    let a : V := ∑ i : Fin r, e i
    let b : V := fun i => if i.val % 2 = 0 then (1 : ZMod p) else 2
    let S : Set V :=
      {x |
        (∃ i : Fin r, x = e i ∨ x = -e i) ∨
          x = a ∨ x = -a ∨ x = b ∨ x = -b}
    0 ∉ S ∧
      (∀ x : V, x ∈ S → -x ∈ S) ∧
      Submodule.span (ZMod p) S = ⊤ ∧
      Fintype.card {x : V // x ∈ S} = 2 * r + 4 ∧
      ∀ T : Set V,
        0 ∉ T →
        (∀ x : V, x ∈ T → -x ∈ T) →
        ordinaryUndirectedCayleyGraphIso_claim60262 S T →
        ∃ L : V ≃ₗ[ZMod p] V, L '' S = T

end MathlibPlus.Open
