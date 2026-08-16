import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

abbrev extensionSpace_claim33152 (p : ℕ) (U : Type*) := U × ZMod p

def distinguishedW_claim33152 (p : ℕ) (U : Type*) [Zero U] : extensionSpace_claim33152 p U :=
  (0, 1)

def translationSet_claim33152 (p : ℕ) (U : Type*) [AddCommGroup U] :
    Set (Equiv.Perm (extensionSpace_claim33152 p U)) :=
  {τ | ∃ v : extensionSpace_claim33152 p U, τ = Equiv.addRight v}

def shearSet_claim33152 (p : ℕ) (U : Type*) [AddCommGroup U]
    [Module (ZMod p) U] (functional : Module.Dual (ZMod p) U) :
    Set (Equiv.Perm (extensionSpace_claim33152 p U)) :=
  {F | ∃ n : ZMod p, ∀ x : extensionSpace_claim33152 p U,
    F x = x + (n * functional x.1) • distinguishedW_claim33152 p U}

noncomputable def affineShearGroup_claim33152 (p : ℕ) (U : Type*) [AddCommGroup U]
    [Module (ZMod p) U] (functional : Module.Dual (ZMod p) U) :
    Subgroup (Equiv.Perm (extensionSpace_claim33152 p U)) :=
  Subgroup.closure
    (translationSet_claim33152 p U ∪ shearSet_claim33152 p U functional)

noncomputable def translationGroup_claim33152 (p : ℕ) (U : Type*) [AddCommGroup U] :
    Subgroup (Equiv.Perm (extensionSpace_claim33152 p U)) :=
  Subgroup.closure (translationSet_claim33152 p U)

def regularElementaryAbelian_claim33152 (p : ℕ) (U : Type*) [AddCommGroup U]
    (H : Subgroup (Equiv.Perm (extensionSpace_claim33152 p U))) : Prop :=
  (∀ a b : H, a * b = b * a) ∧
    (∀ a : H, a ^ p = 1) ∧
      (∀ x y : extensionSpace_claim33152 p U, ∃! h : H, h.1 x = y)

/-- Every regular elementary abelian subgroup of the generated translation/shear
permutation group is conjugate there to the translation subgroup. -/
def mainCentralDifferenceShearConjugacy_claim33152 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)]
    (U : Type*) [AddCommGroup U] [Module (ZMod p) U]
    [FiniteDimensional (ZMod p) U]
    (functional : Module.Dual (ZMod p) U),
    functional ≠ 0 →
      ∀ H : Subgroup (Equiv.Perm (extensionSpace_claim33152 p U)),
        H ≤ affineShearGroup_claim33152 p U functional →
          regularElementaryAbelian_claim33152 p U H →
            ∃ g : Equiv.Perm (extensionSpace_claim33152 p U),
              g ∈ affineShearGroup_claim33152 p U functional ∧
                ∀ h : Equiv.Perm (extensionSpace_claim33152 p U),
                  h ∈ H ↔
                    ∃ t : Equiv.Perm (extensionSpace_claim33152 p U),
                      t ∈ translationGroup_claim33152 p U ∧
                        h = g * t * g⁻¹

end MathlibPlus.Open.FormalizationBatch
