import Mathlib

namespace MathlibPlus.Open.GroupTheory.FiberShearClaim31831

noncomputable section

abbrev F5 := ZMod 5
abbrev V := Fin 4 → F5
abbrev Omega := F5 × V
abbrev C5Power5 := Multiplicative (Fin 5 → F5)

def translationSubgroup : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure (Set.range (fun a : Omega => Equiv.addRight a))

def conjugatedTranslationSubgroup (q : Equiv.Perm Omega) :
    Subgroup (Equiv.Perm Omega) :=
  (translationSubgroup : Subgroup (Equiv.Perm Omega)).map (MulAut.conj q⁻¹)

def fiberShearCondition (f : V → F5) (q : Equiv.Perm Omega) : Prop :=
  ∀ (z : F5) (v : V), q (z, v) = (z + f v, v)

def regularOnOmega (H : Subgroup (Equiv.Perm Omega)) : Prop :=
  ∀ x y : Omega, ∃! h : H, h.1 x = y

/-- Claim 31831: every normalized fiber shear on `F₅ × F₅⁴` conjugates the
translation group to another regular copy of `C₅⁵`. -/
def claim31831 : Prop :=
  ∀ (f : V → F5),
    f 0 = 0 →
      ∃ q : Equiv.Perm Omega,
        fiberShearCondition f q ∧
          let R := translationSubgroup
          let T := conjugatedTranslationSubgroup q
          Nonempty (R ≃* C5Power5) ∧
            Nonempty (T ≃* C5Power5) ∧
              regularOnOmega R ∧ regularOnOmega T

end

end MathlibPlus.Open.GroupTheory.FiberShearClaim31831
