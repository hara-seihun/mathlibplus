import Mathlib

noncomputable section

namespace MathlibPlus.Open.GraphTheory.C4PermutationBatch

abbrev Hpr (p r : ℕ) := Fin r → ZMod p
abbrev Gpr (p r : ℕ) := ZMod 4 × Hpr p r

def saturatedRelation (p r : ℕ) (x y : Gpr p r) : Prop :=
  x.1 ≠ y.1

def oddHallOrbit (p r : ℕ) (x y : Gpr p r) : Prop :=
  ∃ h : Hpr p r, y = (0, h) + x

def c4Orbit (p r : ℕ) (x y : Gpr p r) : Prop :=
  ∃ a : ZMod 4, y = (a, 0) + x

def conjugateOrbit (p r : ℕ) (g : Gpr p r ≃ Gpr p r)
    (orbit : Gpr p r → Gpr p r → Prop) (x y : Gpr p r) : Prop :=
  ∃ z w, g z = x ∧ g w = y ∧ orbit z w

/-- Claim 53681: a within-fibre transposition preserves the odd-Hall
partition, changes the characteristic C₄ partition, and is a graph
conjugator. -/
def regularCopyConjugacyLabels_claim53681 : Prop :=
  ∀ (p r : ℕ), Nat.Prime p → 2 < p → 1 ≤ r →
    let e : Hpr p r := fun i => if i.1 = 0 then 1 else 0
    let v₀ : Gpr p r := (0, 0)
    let v₁ : Gpr p r := (0, e)
    let g : Gpr p r ≃ Gpr p r := Equiv.swap v₀ v₁
    (∀ x, (g x).1 = x.1) ∧
      (∀ x y, saturatedRelation p r x y ↔
        saturatedRelation p r (g x) (g y)) ∧
      (∀ x y, oddHallOrbit p r x y ↔
        conjugateOrbit p r g (oddHallOrbit p r) x y) ∧
      (∃ x y,
        (c4Orbit p r x y ∧ ¬ conjugateOrbit p r g (c4Orbit p r) x y) ∨
        (conjugateOrbit p r g (c4Orbit p r) x y ∧ ¬ c4Orbit p r x y))

end MathlibPlus.Open.GraphTheory.C4PermutationBatch
