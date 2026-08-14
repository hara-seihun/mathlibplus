import Mathlib

namespace MathlibPlus.Open.GroupTheory.NewResearch2.D0137

/-- Claim 5838: a common central C_p^2 subgroup can be normalized in the 2-closure. -/
def claim5838 : Prop :=
  ∀ {Omega : Type*} (p n : ℕ)
    (R T : Subgroup (Equiv.Perm Omega)),
    Nat.Prime p → 2 ≤ n →
      (let regular : Subgroup (Equiv.Perm Omega) → Prop := fun H =>
        ∀ a b : Omega, ∃! g : H, g.1 a = b
       let elementary : Subgroup (Equiv.Perm Omega) → ℕ → Prop := fun H r =>
        Nonempty (H ≃* Multiplicative (Fin r → ZMod p))
       let conjugate : Equiv.Perm Omega → Subgroup (Equiv.Perm Omega) →
           Subgroup (Equiv.Perm Omega) := fun x H =>
         Subgroup.closure {g : Equiv.Perm Omega |
           ∃ h : Equiv.Perm Omega, h ∈ H ∧ g = x⁻¹ * h * x}
       let inTwoClosure : Subgroup (Equiv.Perm Omega) → Equiv.Perm Omega → Prop :=
         fun H g =>
           ∀ a b : Omega, ∃ h : H, g a = h.1 a ∧ g b = h.1 b
       regular R → regular T → elementary R n → elementary T n →
         ∃ x : Equiv.Perm Omega, x ∈ R ⊔ T ∧
           ∃ psi : Equiv.Perm Omega,
             inTwoClosure (R ⊔ conjugate x T) psi ∧
               ∃ D : Subgroup (Equiv.Perm Omega),
                 elementary D 2 ∧ D ≤ R ∧ D ≤ conjugate psi (conjugate x T) ∧
                   ∀ d : Equiv.Perm Omega, d ∈ D →
                     ∀ g : Equiv.Perm Omega,
                       g ∈ R ⊔ conjugate psi (conjugate x T) → d * g = g * d)

end MathlibPlus.Open.GroupTheory.NewResearch2.D0137
