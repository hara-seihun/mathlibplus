import Mathlib

namespace MathlibPlus.Open

/--
The paired module is the quotient permutation representation for the diagonal
subgroup of the two Weyl involutions.  The representation-theoretic notation is
spelled out on the concrete quotient and its complex coordinate functions.
-/
def pairedModuleQuotientRepresentation : Prop :=
  let G₀ := ZMod 2 × ZMod 2
  let G := Multiplicative G₀
  let sum : G₀ →+ ZMod 2 :=
    (AddMonoidHom.fst (ZMod 2) (ZMod 2)) +
      (AddMonoidHom.snd (ZMod 2) (ZMod 2))
  let q : G →* Multiplicative (ZMod 2) := AddMonoidHom.toMultiplicative sum
  let H : Subgroup G := q.ker
  let Q := G ⧸ H
  let π : G →* Q := QuotientGroup.mk' H
  let a : G := Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2))
  let b : G := Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2))
  let χ_rel : G → ℂ := fun g =>
    if q g = (1 : Multiplicative (ZMod 2)) then 1 else -1
  let actQ : G → (Q → ℂ) → (Q → ℂ) := fun g f x =>
    f (π (g⁻¹) * x)
  let actInd : G → (G → ℂ) → (G → ℂ) := fun g f x =>
    f (g⁻¹ * x)
  let actSplit : G → (ℂ × ℂ) → (ℂ × ℂ) := fun g v =>
    (v.1, χ_rel g * v.2)
  Nonempty (Q ≃* Multiplicative (ZMod 2)) ∧
    (χ_rel 1 = 1 ∧
      (∀ g₁ g₂ : G, χ_rel (g₁ * g₂) = χ_rel g₁ * χ_rel g₂)) ∧
    (∃ w : Q → Q,
      (∀ x : Q, w (w x) = x) ∧
        (∀ x : Q, w x ≠ x) ∧
        (∀ x : Q, π a * x = w x) ∧
        (∀ x : Q, π b * x = w x) ∧
        (∀ x : Q, π (a * b) * x = x)) ∧
    (∀ F : G → ℂ,
      (∀ h : H, ∀ g : G, F ((h : G) * g) = F g) ↔
        ∃ f : Q → ℂ, ∀ g : G, F g = f (π g)) ∧
    (∀ g : G, ∀ f : Q → ℂ, ∀ x : G,
      actInd g (fun y => f (π y)) x = actQ g f (π x)) ∧
    (∃ e : (Q → ℂ) ≃ₗ[ℂ] (ℂ × ℂ),
      ∀ g : G, ∀ f : Q → ℂ,
        e (actQ g f) = actSplit g (e f))

end MathlibPlus.Open
