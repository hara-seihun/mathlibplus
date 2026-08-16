import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch60250_60251_60252_60253

def eGeneratorA60251 : FreeGroup (Fin 2) := FreeGroup.of 0
def eGeneratorT60251 : FreeGroup (Fin 2) := FreeGroup.of 1

def eRelations60251 : Set (FreeGroup (Fin 2)) :=
  {eGeneratorA60251 ^ 35,
    eGeneratorT60251 ^ 8,
    eGeneratorT60251 * eGeneratorA60251 * eGeneratorT60251⁻¹ *
      eGeneratorA60251}

abbrev eC35_8_60251 : Type := PresentedGroup eRelations60251

def cayleyGraph60251 (S : Set eC35_8_60251) : SimpleGraph eC35_8_60251 :=
  SimpleGraph.fromRel (fun x y => x⁻¹ * y ∈ S)

def identityFreeInverseClosed60251 (S : Set eC35_8_60251) : Prop :=
  S ⊆ {x | x ≠ 1} ∧ ∀ x, x ∈ S → x⁻¹ ∈ S

def Claim60251 : Prop :=
  ∀ S T : Set eC35_8_60251,
    identityFreeInverseClosed60251 S ∧ identityFreeInverseClosed60251 T ∧
      ((S.ncard = 8 ∧ T.ncard = 8) ∨
        (S.ncard = 271 ∧ T.ncard = 271)) →
    (cayleyGraph60251 S ≃g cayleyGraph60251 T) →
    ∃ α : MulAut eC35_8_60251, α '' S = T

end MathlibPlus.Open.ResearchFormalization.Batch60250_60251_60252_60253
