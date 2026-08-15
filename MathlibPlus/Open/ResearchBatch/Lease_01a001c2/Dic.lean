import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Dic

noncomputable section
open Classical

abbrev Q220 := ZMod 11 × ZMod 5 × ZMod 4

def dicSign (i : ZMod 4) : ℤ :=
  if i.val % 2 = 0 then 1 else -1

def dicMul (u v : Q220) : Q220 :=
  (u.1 + (dicSign u.2.2 : ZMod 11) * v.1,
    u.2.1 + (dicSign u.2.2 : ZMod 5) * v.2.1,
    u.2.2 + v.2.2)

def dicOne : Q220 := (0, 0, 0)
def dicInvolution : Q220 := (0, 0, 2)

def inverseAtom (u v : Q220) : Prop :=
  dicMul u v = dicOne ∧ dicMul v u = dicOne

def centralForDic (u : Q220) : Prop :=
  ∀ v : Q220, dicMul u v = dicMul v u

/-- Claim 32823.  The final conjunct states the singleton inverse atom and
109 inverse pairs directly through the inverse relation. -/
def claim_32823 : Prop :=
  Fintype.card Q220 = 220 ∧
    dicOne = (0, 0, 0) ∧ dicInvolution = (0, 0, 2) ∧
    dicMul dicInvolution dicInvolution = dicOne ∧
    dicInvolution ≠ dicOne ∧ centralForDic dicInvolution ∧
    (∀ u v : Q220, inverseAtom u v →
      ∃! w : Q220, inverseAtom u w) ∧
    Nonempty ({u : Q220 // u ≠ dicOne} ≃ Fin 219) ∧
    Nonempty ({u : Q220 // u ≠ dicOne ∧ inverseAtom u u} ≃ Fin 1) ∧
    Nonempty ({u : Q220 // u ≠ dicOne ∧ u ≠ dicInvolution} ≃ Fin 218) ∧
    ∃ r : Fin 109 → Q220,
      (∀ i, r i ≠ dicOne ∧ r i ≠ dicInvolution ∧
        ∃! v : Q220, inverseAtom (r i) v ∧ v ≠ r i) ∧
      (∀ i j, i ≠ j → r i ≠ r j ∧
        ∀ v, ¬(inverseAtom (r i) v ∧ (v = r j ∨ inverseAtom (r j) v))) ∧
      (∀ u : Q220, u ≠ dicOne →
        u = dicInvolution ∨ ∃ i : Fin 109,
          u = r i ∨ ∃ v : Q220, inverseAtom (r i) v ∧ u = v)

end
end MathlibPlus.Open.ResearchBatch.Dic
