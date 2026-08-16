import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

noncomputable section

abbrev F5 := ZMod 5
abbrev W := Fin 3 → F5
abbrev U := W
abbrev V := W × U

noncomputable def L16 : Matrix (Fin 3) (Fin 3) F5 :=
  ![![3, 4, 1], ![0, 2, 0], ![0, 0, 2]]

noncomputable def L49_1 : Matrix (Fin 3) (Fin 3) F5 :=
  ![![1, 1, 0], ![4, 2, 0], ![0, 1, 1]]

noncomputable def L49_2 : Matrix (Fin 3) (Fin 3) F5 :=
  ![![0, 3, 0], ![4, 4, 0], ![4, 4, 1]]

def sigma49 (w : W) : W :=
  (![w 0, w 1, w 2 + (w 0) ^ 3 * (w 1) ^ 2] : W)

noncomputable def q16 (w : W) : W :=
  Matrix.mulVec L16
    (![w 0 + 4 * (w 1) ^ 3 * (w 2) ^ 2, w 1, w 2] : W)

noncomputable def q49 (w : W) : W :=
  sigma49 (Matrix.mulVec L49_2 (Matrix.mulVec L49_1 w))

def claim60617 : Prop :=
  (IsUnit (Matrix.det L16) ∧
      IsUnit (Matrix.det L49_1) ∧
      IsUnit (Matrix.det L49_2)) ∧
    Function.Odd q16 ∧ Function.Odd q49

noncomputable def tau (q : W ≃ W) (v s : W) : W :=
  q.symm (q (v + s) - q v)

def generator (q : W ≃ W) (s t : W) : Prop :=
  ∃ v : W, t = tau q v s ∨ t = -tau q v s

noncomputable def sameBlock (P : Finset (Finset W)) (s t : W) : Prop :=
  letI : DecidableEq W := Classical.decEq W
  ∃ B ∈ P, s ∈ B ∧ t ∈ B

noncomputable def generatedPartition (q : W ≃ W) (P : Finset (Finset W)) : Prop :=
  letI : DecidableEq W := Classical.decEq W
  (∀ B ∈ P, B.Nonempty) ∧
    (∀ x : W, ∃ B ∈ P, x ∈ B) ∧
    (∀ B ∈ P, ∀ C ∈ P, B ≠ C → ∀ x : W, x ∈ B → x ∉ C) ∧
    (∀ s t : W, sameBlock P s t ↔ Relation.EqvGen (generator q) s t)

def stableUnderNegation (P : Finset (Finset W)) : Prop :=
  letI : DecidableEq W := Classical.decEq W
  ∀ B ∈ P, ∀ s ∈ B, -s ∈ B

def expectedBlockSizes : Multiset Nat :=
  Multiset.ofList ([1, 2, 2] ++ List.replicate 12 10)

def claim60618 : Prop :=
  ∀ q : W ≃ W, (q.toFun = q16 ∨ q.toFun = q49) →
    ∃ P : Finset (Finset W),
      generatedPartition q P ∧
        Multiset.map Finset.card P.1 = expectedBlockSizes ∧
        stableUnderNegation P

end
end MathlibPlus.Open.Research.FormalizationBatch
