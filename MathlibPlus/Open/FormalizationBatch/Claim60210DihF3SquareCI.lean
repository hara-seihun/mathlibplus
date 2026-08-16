import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.CayleyCI

/-- Claim 60210: the generalized dihedral group of `(F_3)^2` is an
undirected CI-group.  The carrier is represented by its sign unit and
vector coordinates, with the displayed multiplication and inverse. -/
def dih_f3_square_undirected_ci : Prop :=
  let V := Fin 2 → ZMod 3
  let G := (ZMod 3)ˣ × V
  let one : G := (1, 0)
  let mul : G → G → G := fun g h =>
    (g.1 * h.1, g.2 + (g.1 : ZMod 3) • h.2)
  let inv : G → G := fun g =>
    (g.1⁻¹, -((g.1⁻¹ : ZMod 3) • g.2))
  let phi : (V ≃ₗ[ZMod 3] V) → V → G → G := fun M c g =>
    if g.1 = (1 : (ZMod 3)ˣ) then
      (1, M g.2)
    else
      (g.1, M g.2 + c)
  let cayley : Set G → SimpleGraph G := fun S =>
    SimpleGraph.fromRel (fun g h => mul g (inv h) ∈ S)
  ∀ (S T : Set G),
    one ∉ S →
    one ∉ T →
    (∀ g, g ∈ S → inv g ∈ S) →
    (∀ g, g ∈ T → inv g ∈ T) →
    SimpleGraph.Iso (cayley S) (cayley T) →
    ∃ (M : V ≃ₗ[ZMod 3] V) (c : V),
      Function.Bijective (phi M c) ∧
      (∀ g h, phi M c (mul g h) = mul (phi M c g) (phi M c h)) ∧
      phi M c one = one ∧
      (∀ g, phi M c (inv g) = inv (phi M c g)) ∧
      (∀ x, phi M c (1, x) = (1, M x)) ∧
      (∀ x, phi M c (-1, x) = (-1, M x + c)) ∧
      (∀ g, g ∈ S ↔ phi M c g ∈ T)

end MathlibPlus.Open.FormalizationBatch.CayleyCI
