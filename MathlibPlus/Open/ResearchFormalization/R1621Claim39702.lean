import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39702

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

noncomputable section

abbrev SubgroupOfAffineBorel7 :=
  {Γ : Subgroup Perm7 // Γ ≤ affineBorel7}

def linearImageSet7 (K : Subgroup Perm7) : Set linearBorel7 :=
  {b | ∃ g : K, ∃ t : W7,
    ∀ z : W7, (g : Perm7) z = t + (b : Perm7) z}

def linearImageOrder7 (K : Subgroup Perm7) : ℕ :=
  Nat.card {b : linearBorel7 // b ∈ linearImageSet7 K}

def exceptionalExcess7 (Γ : SubgroupOfAffineBorel7) : Prop :=
  strictlyContains7 (translationCore7 Γ.1) (translationStabilizer7 Γ.1)

def persistentExceptionalConfiguration7
    (Γ : SubgroupOfAffineBorel7) (groupOrder linearOrder : ℕ) : Prop :=
  exceptionalExcess7 Γ ∧
    Nat.card Γ.1 = groupOrder ∧
      linearImageOrder7 Γ.1 = linearOrder ∧
        Nat.card (heisenbergCore7 Γ.1) = 49 ∧
          transitive7 (heisenbergCore7 Γ.1) ∧
            translationCore7 (heisenbergCore7 Γ.1) = flagVectors7 ∧
              translationCore7 Γ.1 = flagVectors7 ∧
                translationStabilizer7 Γ.1 = (Set.univ : Set W7)

/-- Claim 39702: the universal translation-core equality is false, and all
four paired exceptional orders occur with the stated flag-line core shape. -/
def claim39702_translationCoreCounterfeitFalse : Prop :=
  ¬ (∀ Γ : SubgroupOfAffineBorel7,
      translationStabilizer7 Γ.1 = translationCore7 Γ.1) ∧
    (∃ Γ : SubgroupOfAffineBorel7,
      persistentExceptionalConfiguration7 Γ 49 7) ∧
      (∃ Γ : SubgroupOfAffineBorel7,
        persistentExceptionalConfiguration7 Γ 98 14) ∧
        (∃ Γ : SubgroupOfAffineBorel7,
          persistentExceptionalConfiguration7 Γ 147 21) ∧
          (∃ Γ : SubgroupOfAffineBorel7,
            persistentExceptionalConfiguration7 Γ 294 42)

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39702
