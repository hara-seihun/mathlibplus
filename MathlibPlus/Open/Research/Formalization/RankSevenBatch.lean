import Mathlib

namespace MathlibPlus.Open.Research.RankSevenBatch

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev H5 := Fin 5 → ZMod 3

 def hTranslation (h : H5) : Equiv.Perm H5 :=
  { toFun := fun v => fun k => v k + h k
    invFun := fun v => fun k => v k - h k
    left_inv := by
      intro v
      funext k
      simp
    right_inv := by
      intro v
      funext k
      simp }

def rankSevenX : Equiv.Perm H5 :=
  { toFun := fun v => ![v 0, v 1, v 2 + v 0, v 3 + v 1, v 4]
    invFun := fun v => ![v 0, v 1, v 2 - v 0, v 3 - v 1, v 4]
    left_inv := by
      intro v
      funext k
      fin_cases k <;> simp
    right_inv := by
      intro v
      funext k
      fin_cases k <;> simp }

def rankSevenY : Equiv.Perm H5 :=
  { toFun := fun v => ![v 0, v 1, v 2, v 3 + v 0, v 4 + v 1]
    invFun := fun v => ![v 0, v 1, v 2, v 3 - v 0, v 4 - v 1]
    left_inv := by
      intro v
      funext k
      fin_cases k <;> simp
    right_inv := by
      intro v
      funext k
      fin_cases k <;> simp }

def regularTranslations : Set (Equiv.Perm H5) :=
  {p | ∃ h : H5, p = hTranslation h}

def H_R : Subgroup (Equiv.Perm H5) :=
  Subgroup.closure regularTranslations

def rankSevenXGroup : Subgroup (Equiv.Perm H5) :=
  Subgroup.closure (regularTranslations ∪ {rankSevenX, rankSevenY})

def rankSevenL : Subgroup (Equiv.Perm H5) :=
  Subgroup.closure ({rankSevenX, rankSevenY} : Set (Equiv.Perm H5))

def claim_32852 : Prop :=
  Nat.card (rankSevenXGroup : Type) = 3 ^ 7 ∧
    Nat.card (rankSevenL : Type) = 9

end
end MathlibPlus.Open.Research.RankSevenBatch
