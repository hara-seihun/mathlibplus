import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R1522

abbrev Cycle28 := ZMod 28

def cycleShift : Equiv.Perm Cycle28 :=
  { toFun := fun x => x + 1
    invFun := fun x => x - 1
    left_inv := by intro x; simp
    right_inv := by intro x; simp }

def layerSame (x y : Cycle28) : Prop := x.val % 4 = y.val % 4
def doubleTransposition (a b c d : Cycle28) : Equiv.Perm Cycle28 :=
  Equiv.swap a b * Equiv.swap c d
def admissiblePosition (a b c d : Cycle28) : Prop :=
  a ≠ b ∧ c ≠ d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
    ¬ layerSame a b ∧ ¬ layerSame c d

def affineGenerators : Set (Equiv.Perm Cycle28) :=
  {g | ∃ b : Cycle28, ∃ u : (ZMod 28)ˣ,
    ∀ x : Cycle28, g x = b + (u : Cycle28) * x}

def cyclicAffineSubgroup : Subgroup (Equiv.Perm Cycle28) :=
  Subgroup.closure affineGenerators

def normalizedTwoCrossLayerFamily_claim38095 : Prop :=
  (∀ a b c d : Cycle28,
    admissiblePosition a b c d →
      doubleTransposition a b c d =
        Equiv.swap a b * Equiv.swap c d) ∧
  Subgroup.normalizer (Subgroup.zpowers cycleShift : Set (Equiv.Perm Cycle28)) =
      cyclicAffineSubgroup ∧
  Nat.card (Subgroup.normalizer
    (Subgroup.zpowers cycleShift : Set (Equiv.Perm Cycle28))) = 336

def exceptionalTau : Equiv.Perm Cycle28 :=
  doubleTransposition 0 2 14 16
def exceptionalH : Equiv.Perm Cycle28 := exceptionalTau * cycleShift * exceptionalTau
def exceptionalF : Equiv.Perm Cycle28 := cycleShift⁻¹ * cycleShift⁻¹ * exceptionalTau
def oddResidues : Set Cycle28 := {x | x.val % 2 = 1}
def nonzeroEvenExcept14 : Set Cycle28 :=
  {x | x ≠ 0 ∧ x ≠ 14 ∧ x.val % 2 = 0}

def exceptionalChart_claim38101 : Prop :=
  exceptionalF 0 = 0 ∧
  exceptionalF * exceptionalH = cycleShift * exceptionalF ∧
  Set.MapsTo exceptionalF {0} {0} ∧
  Set.MapsTo exceptionalF oddResidues oddResidues ∧
  Set.MapsTo exceptionalF nonzeroEvenExcept14 nonzeroEvenExcept14 ∧
  Set.MapsTo exceptionalF {14} {14}

end MathlibPlus.Open.ResearchBatch.R1522
