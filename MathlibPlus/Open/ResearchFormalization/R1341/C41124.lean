import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1341C41124

noncomputable section

abbrev FunctionModule (H : Type*) := H → ZMod 3

def translateFunction {H : Type*} [Add H]
    (p : H) (k : FunctionModule H) : FunctionModule H :=
  fun x => k (x + p)

def translationInvariantModule
    {H : Type*} [AddCommGroup H] [Fintype H]
    (K : Submodule (ZMod 3) (FunctionModule H)) : Prop :=
  ∀ p : H, ∀ k : FunctionModule H, k ∈ K → translateFunction p k ∈ K

def commonPeriodCondition
    {H : Type*} [AddCommGroup H]
    (K : Submodule (ZMod 3) (FunctionModule H))
    (P : AddSubgroup H) : Prop :=
  ∀ p : H, p ∈ P ↔
    ∀ k : FunctionModule H, k ∈ K →
      ∀ x : H, k (x + p) = k x

def cosetConstantOn
    {H : Type*} [AddCommGroup H]
    (P : AddSubgroup H) (k : FunctionModule H) : Prop :=
  ∀ x : H, ∀ p : P, k (x + p.1) = k x

def quotientInflation
    {H : Type*} [AddCommGroup H]
    (P : AddSubgroup H) (g : (H ⧸ P) → ZMod 3) : FunctionModule H :=
  fun x => g (QuotientAddGroup.mk x)

/-- Claim 41124: a positive common period is exactly a quotient-coset
inflation for a translation-invariant function module. -/
def claim41124_positivePeriodQuotientInflation : Prop :=
  ∀ (H : Type*) [AddCommGroup H] [Fintype H]
    (K : Submodule (ZMod 3) (FunctionModule H))
    (P : AddSubgroup H),
    translationInvariantModule K → P ≠ ⊥ → commonPeriodCondition K P →
    (∀ k : FunctionModule H, k ∈ K → cosetConstantOn P k) ∧
      ∃ Kbar : Submodule (ZMod 3) ((H ⧸ P) → ZMod 3),
        ∀ k : FunctionModule H,
          k ∈ K ↔ ∃ g : (H ⧸ P) → ZMod 3,
            g ∈ Kbar ∧ k = quotientInflation P g

end

end MathlibPlus.Open.ResearchFormalization.R1341C41124
