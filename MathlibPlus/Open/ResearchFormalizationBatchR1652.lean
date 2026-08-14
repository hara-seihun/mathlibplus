import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatchR1652

abbrev LocalPoint5 := ZMod 5
abbrev LocalPermutation5 := Equiv.Perm LocalPoint5
abbrev OuterBlock8 := Fin 8

/-- The local affine permutations in `AGL(1,5)`. -/
def isAffineOneFive (σ : LocalPermutation5) : Prop :=
  ∃ a b : ZMod 5, a ≠ 0 ∧ ∀ x : ZMod 5, σ x = a * x + b

def threeBlockChart5
    (τ σ₁ σ₂ : LocalPermutation5) (i j : OuterBlock8) :
    OuterBlock8 → LocalPermutation5 :=
  fun b => if b = 0 then τ else if b = i then σ₁ else if b = j then σ₂ else Equiv.refl _

/-- Claim 32966: exactly three nonidentity local entries with one nonaffine entry. -/
def exactlyThreeBlockUnequalAffineChartFamily
    (F : OuterBlock8 → LocalPermutation5) : Prop :=
  ∃ (τ σ₁ σ₂ : LocalPermutation5) (i j : OuterBlock8),
    1 ≤ i.val ∧ i.val < j.val ∧ j.val ≤ 7 ∧
    ¬ isAffineOneFive τ ∧
    isAffineOneFive σ₁ ∧ isAffineOneFive σ₂ ∧
    σ₁ ≠ Equiv.refl _ ∧ σ₂ ≠ Equiv.refl _ ∧ σ₁ ≠ σ₂ ∧
    F = threeBlockChart5 τ σ₁ σ₂ i j

end MathlibPlus.Open.ResearchFormalizationBatchR1652
