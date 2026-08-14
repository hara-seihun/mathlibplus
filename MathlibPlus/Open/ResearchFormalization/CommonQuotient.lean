import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

private def Orbit {Ω : Type*} (P : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ g : P, g.1 x = y}

private def IsRegularSubgroup {Ω : Type*} (S : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! g : S, g.1 x = y

private def IsInternalDirectProduct {Ω : Type*}
    (R P A : Subgroup (Equiv.Perm Ω)) : Prop :=
  P ≤ R ∧ A ≤ R ∧ R = P ⊔ A ∧ Disjoint P A ∧
    ∀ p : P, ∀ a : A, (p.1 : Equiv.Perm Ω) * a.1 = a.1 * p.1

private def IsCharacteristicSubgroup {Ω : Type*}
    (P R : Subgroup (Equiv.Perm Ω)) : Prop :=
  P ≤ R ∧ ∀ σ : R ≃* R, ∀ x : R,
    (((x.1 : Equiv.Perm Ω) ∈ P) ↔ ((σ x).1 : Equiv.Perm Ω) ∈ P)

private def IsCpPower {Ω : Type*} (S : Subgroup (Equiv.Perm Ω))
    (p r : ℕ) (hp : Nat.Prime p) : Prop :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  Nonempty (S ≃* Multiplicative (Fin r → ZMod p))

private def SameOrbitPartition {Ω : Type*}
    (P Q : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, (y ∈ Orbit P x) ↔ (y ∈ Orbit Q x)

private def SameInducedQuotientAction {Ω : Type*}
    (P R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ r : R, ∃ t : T, ∀ x : Ω, Orbit P (r.1 x) = Orbit P (t.1 x)) ∧
  (∀ t : T, ∃ r : R, ∀ x : Ω, Orbit P (t.1 x) = Orbit P (r.1 x))

private def IsBlockKernel {Ω : Type*}
    (P M K : Subgroup (Equiv.Perm Ω)) : Prop :=
  K ≤ M ∧ ∀ k : Equiv.Perm Ω,
    (k ∈ K ↔ k ∈ M ∧ ∀ x : Ω, Orbit P (k x) = Orbit P x)

private def IsPGroup {Ω : Type*} [Fintype Ω]
    (K : Subgroup (Equiv.Perm Ω)) (p : ℕ) : Prop :=
  letI := Fintype.ofFinite K
  ∃ n : ℕ, Fintype.card K = p ^ n

private def ConjugateBySubgroup {Ω : Type*}
    (A B K : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ k : K, ∀ a : Equiv.Perm Ω,
    (a ∈ A ↔ (k.1 * a * k.1⁻¹) ∈ B)

/-- Exact open formulation of the admitted common-quotient, `p`-kernel theorem. -/
def claim30408 : Prop :=
  ∀ (p r : ℕ) (H Ω : Type*) [Fintype Ω] [Fintype H] [Group H]
    (hp : Nat.Prime p),
    ¬ p ∣ Fintype.card H →
    ∀ (P Q A B R T M K : Subgroup (Equiv.Perm Ω)),
      IsRegularSubgroup R →
      IsRegularSubgroup T →
      Nonempty (R ≃* (Multiplicative (Fin r → ZMod p) × H)) →
      Nonempty (T ≃* (Multiplicative (Fin r → ZMod p) × H)) →
      IsInternalDirectProduct R P A →
      IsInternalDirectProduct T Q B →
      IsCpPower P p r hp →
      IsCpPower Q p r hp →
      Nonempty (A ≃* H) →
      Nonempty (B ≃* H) →
      IsCharacteristicSubgroup P R →
      IsCharacteristicSubgroup Q T →
      SameOrbitPartition P Q →
      SameInducedQuotientAction P R T →
      M = R ⊔ T →
      IsBlockKernel P M K →
      IsPGroup K p →
      ConjugateBySubgroup A B K

end MathlibPlus.Open.ResearchFormalization
