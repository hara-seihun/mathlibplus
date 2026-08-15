import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R1584Counterexample

abbrev S5 := Equiv.Perm (Fin 5)
abbrev S7 := Equiv.Perm (Fin 7)

def equalSignFiber : Subgroup (S5 × S7) :=
  { carrier := {p | Equiv.Perm.sign p.1 = Equiv.Perm.sign p.2}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      simpa using congrArg₂ (· * ·) ha hb
    inv_mem' := by
      intro a ha
      simpa using congrArg (fun z => z⁻¹) ha }

def nonperfectParityFiberProduct_claim39388 : Prop :=
  (letI : Fintype equalSignFiber := Fintype.ofFinite equalSignFiber
   Fintype.card equalSignFiber = 302400) ∧
  Fintype.card (S5 × S7) = 604800 ∧
  equalSignFiber < ⊤ ∧
  (∀ g : S5, ∃ h : S7, (g, h) ∈ equalSignFiber) ∧
  (∀ h : S7, ∃ g : S5, (g, h) ∈ equalSignFiber)

end MathlibPlus.Open.ResearchBatch.R1584Counterexample
