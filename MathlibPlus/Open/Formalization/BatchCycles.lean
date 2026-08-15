import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

private def involution {Ω : Type} (ι : Equiv.Perm Ω) : Prop :=
  ∀ x : Ω, ι (ι x) = x

private def oneFixedPoint {Ω : Type} [DecidableEq Ω]
    (ι : Equiv.Perm Ω) : Prop :=
  ∃ a : Ω, ∀ x : Ω, ι x = x ↔ x = a

private def regularPCycle {Ω : Type} [Fintype Ω] (p : Nat)
    (c : Equiv.Perm Ω) : Prop :=
  ∀ x : Ω, Set.range (fun n : Fin p => (c ^ (n : Nat)) x) = Set.univ

private def compatibleReflection {Ω : Type} (ι c : Equiv.Perm Ω) : Prop :=
  ι * c * ι = c⁻¹

/-- Claim 54503: reflection-compatible odd prime cycles are conjugate. -/
def claim_54503 {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p : Nat) (ι κ c d : Equiv.Perm Ω) : Prop :=
  Nat.Prime p → Fintype.card Ω = p → p % 2 = 1 →
  involution ι ∧ involution κ ∧ oneFixedPoint ι ∧ oneFixedPoint κ →
  regularPCycle p c ∧ regularPCycle p d →
  compatibleReflection ι c ∧ compatibleReflection κ d →
  (∃ h : Equiv.Perm Ω,
      h * c * h⁻¹ = d ∧ h * ι * h⁻¹ = κ) ∧
  (∀ c d : Equiv.Perm Ω,
      regularPCycle p c → regularPCycle p d →
      compatibleReflection ι c → compatibleReflection ι d →
      ∃ h : Equiv.Perm Ω,
        h * ι = ι * h ∧ h * c * h⁻¹ = d)

/-- Claim 54505: the exact compatible-cycle count and transitivity. -/
def claim_54505 {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p : Nat) (ι : Equiv.Perm Ω) : Prop := by
  classical
  let C : Finset (Equiv.Perm Ω) :=
    Finset.univ.filter (fun c => regularPCycle p c ∧ compatibleReflection ι c)
  let Cι : Finset (Equiv.Perm Ω) :=
    Finset.univ.filter (fun h => h * ι = ι * h)
  exact
    Nat.Prime p → Fintype.card Ω = p → p % 2 = 1 →
    involution ι → oneFixedPoint ι →
    C.card = 2 ^ ((p - 1) / 2) * Nat.factorial ((p - 1) / 2) ∧
    Cι.card = 2 ^ ((p - 1) / 2) * Nat.factorial ((p - 1) / 2) ∧
    (∀ ⦃c d : Equiv.Perm Ω⦄, c ∈ C → d ∈ C →
      ∃ h ∈ Cι, h * c * h⁻¹ = d)

end
end MathlibPlus.Open.FormalizationBatch
