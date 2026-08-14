import Mathlib

noncomputable section

namespace MathlibPlus.Open.GroupTheory

private def regularOn {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! g : G, (g : Equiv.Perm Ω) x = y
private def twoClosure {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {q | ∀ x y : Ω, ∃ g : G, q x = (g : Equiv.Perm Ω) x ∧ q y = (g : Equiv.Perm Ω) y}

/-- Claim 28227: the displayed transporter conjugates the regular groups inside the exact 2-closure. -/
def claim28227 {Ω : Type*}
    (T Tq : Subgroup (Equiv.Perm Ω)) (qφ : Equiv.Perm Ω) : Prop :=
  regularOn T ∧ regularOn Tq ∧
    (∀ u : Equiv.Perm Ω,
      u ∈ Tq ↔ ∃ v : Equiv.Perm Ω, v ∈ T ∧ u = qφ⁻¹ * v * qφ) ∧
    qφ ∈ twoClosure (Subgroup.closure (T ⊔ Tq))

end MathlibPlus.Open.GroupTheory
