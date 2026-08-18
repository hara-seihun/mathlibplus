import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1575Claim39301

namespace MathlibPlus.Open.ResearchFormalization.R1575Claim39306

noncomputable section
open scoped Classical

abbrev F7 := MathlibPlus.Open.ResearchFormalization.R1575Claim39301.F7
abbrev W := MathlibPlus.Open.ResearchFormalization.R1575Claim39301.W
abbrev HeisenbergPoint :=
  MathlibPlus.Open.ResearchFormalization.R1575Claim39301.HeisenbergPoint

open MathlibPlus.Open.ResearchFormalization.R1575Claim39301

def allSubgroups : Finset (Finset HeisenbergPoint) :=
  Finset.univ.filter
    (fun S => heisSubgroup (S : Set HeisenbergPoint))

def nonzeroShearProjection (S : Finset HeisenbergPoint) : Prop :=
  ∃ g : HeisenbergPoint, g ∈ (S : Set HeisenbergPoint) ∧ g.1 ≠ 0

def ambientCenterOrder (S : Finset HeisenbergPoint) : Nat :=
  Set.ncard ((S : Set HeisenbergPoint) ∩ heisenbergU)

def translationOrder (S : Finset HeisenbergPoint) : Nat :=
  Set.ncard (translationStabilizer (S : Set HeisenbergPoint))

def subgroupCellNoVertical
    (order rank center translations : Nat) : Nat :=
  (allSubgroups.filter
    (fun S =>
      nonzeroShearProjection S ∧
        S.card = order ∧
          projectionDimension (S : Set HeisenbergPoint) = rank ∧
            ambientCenterOrder S = center ∧
              ¬ verticalProjectionNonzero (S : Set HeisenbergPoint) ∧
                translationOrder S = translations)).card

def subgroupCellVertical
    (order rank center translations : Nat) : Nat :=
  (allSubgroups.filter
    (fun S =>
      nonzeroShearProjection S ∧
        S.card = order ∧
          projectionDimension (S : Set HeisenbergPoint) = rank ∧
            ambientCenterOrder S = center ∧
              verticalProjectionNonzero (S : Set HeisenbergPoint) ∧
                translationOrder S = translations)).card

def claim_39306 : Prop :=
  heisGroupLaws ∧
    Fintype.card HeisenbergPoint = 343 ∧
      allSubgroups.card = 67 ∧
        (allSubgroups.filter nonzeroShearProjection).card = 57 ∧
          subgroupCellNoVertical 7 1 1 1 = 7 ∧
            subgroupCellVertical 7 1 1 1 = 42 ∧
              subgroupCellNoVertical 49 1 7 7 = 1 ∧
                subgroupCellVertical 49 1 7 49 = 6 ∧
                  subgroupCellVertical 343 2 7 49 = 1

end

end MathlibPlus.Open.ResearchFormalization.R1575Claim39306
