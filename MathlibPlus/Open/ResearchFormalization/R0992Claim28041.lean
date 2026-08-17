import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28041

noncomputable section
open Classical

abbrev F3 := ZMod 3
abbrev Plane := F3 × F3
abbrev Output := Fin 3 → F3

/-- Translation-periodicity of a coefficient table on the exact plane carrier. -/
def tablePeriod (F : Plane → Output) (s : Plane) : Prop :=
  ∀ x : Plane, F (x + s) = F x

def hasNontrivialPeriod (F : Plane → Output) : Prop :=
  ∃ s : Plane, s ≠ 0 ∧ tablePeriod F s

def normalizedTable (F : Plane → Output) : Prop :=
  F 0 = 0

def normalizedPeriodicTable (F : Plane → Output) : Prop :=
  normalizedTable F ∧ hasNontrivialPeriod F

/-- A table factors through the cosets of a line when it is constant on
pairs whose difference lies in that line. -/
def factorsThroughLine (F : Plane → Output)
    (L : Submodule F3 Plane) : Prop :=
  ∀ x y : Plane, x - y ∈ L → F x = F y

/-- The three displayed quotient values are allowed to coincide in the
rank-zero and rank-one cases. -/
def hasQuotientValues (F : Plane → Output) : Prop :=
  ∃ A B : Output, Set.range F ⊆ ({0, A, B} : Set Output)

noncomputable def imageRank (F : Plane → Output) : ℕ :=
  Module.finrank F3 (Submodule.span F3 (Set.range F))

noncomputable def periodicTables : Finset (Plane → Output) := by
  exact (Finset.univ : Finset (Plane → Output)).filter normalizedPeriodicTable

noncomputable def rankTables (r : ℕ) : Finset (Plane → Output) := by
  exact periodicTables.filter (fun F => imageRank F = r)

/-- Restoring constants only in the rank-two normalized residual. -/
noncomputable def restoredRankTwoTables : Finset (Plane → Output) := by
  exact
    (rankTables 2).product (Finset.univ : Finset Output) |>.image
      (fun p => fun x => p.1 x + p.2)

/-- There are exactly four one-dimensional subspaces of the coefficient
plane. -/
def fourPlaneLines : Prop :=
  Nat.card {L : Submodule F3 Plane // Module.finrank F3 L = 1} = 4

/-- Claim 28041: every normalized periodic table factors through one of the
four plane lines with the displayed quotient-value form, and the exact
ranked and rank-two constant-restored censuses hold. -/
def exactPeriodicHomogeneousResidual_claim28041 : Prop :=
  fourPlaneLines ∧
    (∀ F : Plane → Output,
      normalizedPeriodicTable F →
        ∃ L : Submodule F3 Plane,
          Module.finrank F3 L = 1 ∧
            factorsThroughLine F L ∧
              hasQuotientValues F) ∧
    (rankTables 0).card = 1 ∧
      (rankTables 1).card = 416 ∧
        (rankTables 2).card = 2496 ∧
          (rankTables 3).card = 0 ∧
            (rankTables 2).card = 4 * 624 ∧
              restoredRankTwoTables.card = 67392

end
end MathlibPlus.Open.ResearchFormalization.R0992Claim28041
