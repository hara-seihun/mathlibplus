import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.PrimeCycleClaims

local instance fact7 : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev Point7 := ZMod 7

def regularCycle7 : Equiv.Perm Point7 := Equiv.addRight 1

def conjugate7 (g h : Equiv.Perm Point7) : Equiv.Perm Point7 := h⁻¹ * g * h

def primeCycleDerivative7 (σ : Equiv.Perm Point7) : Equiv.Perm Point7 :=
  regularCycle7⁻¹ * conjugate7 regularCycle7 σ

def primeCycleNormalClosure7 (σ : Equiv.Perm Point7) :
    Subgroup (Equiv.Perm Point7) :=
  Subgroup.closure
    (Set.range (fun k : Fin 7 =>
      conjugate7 (primeCycleDerivative7 σ) (regularCycle7 ^ (k : ℕ))))

def claim_38848 : Prop :=
  ∀ σ : Equiv.Perm Point7,
    primeCycleDerivative7 σ =
        regularCycle7⁻¹ * (σ⁻¹ * regularCycle7 * σ) ∧
      primeCycleNormalClosure7 σ =
        Subgroup.closure
          (Set.range (fun k : Fin 7 =>
            (regularCycle7 ^ (k : ℕ))⁻¹ * primeCycleDerivative7 σ *
              regularCycle7 ^ (k : ℕ)))

end MathlibPlus.Open.ResearchFormalization.PrimeCycleClaims
