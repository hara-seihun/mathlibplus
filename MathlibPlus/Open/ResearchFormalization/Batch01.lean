import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- A regular permutation copy of `C_p^n` on `Ω`. -/
def IsRegularCpPower
    {Ω : Type*} [Fintype Ω]
    (p n : ℕ) [Fact p.Prime]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nonempty (R ≃* Multiplicative (Fin n → ZMod p)) ∧
    ∀ x y : Ω, ∃! r : R, r.1 x = y

/-- A literal common central plane for two regular permutation copies. -/
def literalCommonCentralPlane
    {Ω : Type*} [Fintype Ω]
    (p n : ℕ) [Fact p.Prime]
    (R T D : Subgroup (Equiv.Perm Ω)) : Prop :=
  IsRegularCpPower p n R ∧
    IsRegularCpPower p n T ∧
    Nonempty (D ≃* Multiplicative (ZMod p × ZMod p)) ∧
    D ≤ R ⊓ T ∧
    ∀ d : D, ∀ x : ↥(R ⊔ T), d.1 * x.1 = x.1 * d.1

end MathlibPlus.Open.ResearchFormalization
