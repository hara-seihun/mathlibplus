import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch0315

abbrev Coordinate := Fin 6
abbrev TightIndex := Fin 3
abbrev Family := Finset (Finset Coordinate)
abbrev WeightedFamily := Multiset (Finset Coordinate)

def t (i : TightIndex) : Coordinate :=
  ⟨i.val, by omega⟩

def z (i : TightIndex) : Coordinate :=
  ⟨i.val + 3, by omega⟩

def T : Finset Coordinate := {0, 1, 2}

def Z : Finset Coordinate := {3, 4, 5}

def X : Finset Coordinate := Finset.univ

def R (i : TightIndex) : Finset Coordinate := Z ∪ {t i}

def H : Family :=
  ({∅} : Family) ∪
    ((T.powerset.erase (∅ : Finset Coordinate)).image (fun S => Z ∪ S))

def unionClosed (F : Family) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

def projectsToT (F : Family) : Prop :=
  F.image (fun A => A ∩ T) = T.powerset

def removable (F : Family) (A : Finset Coordinate) : Prop :=
  A ∈ F ∧ unionClosed (F.erase A)

def mandatoryThreeGeneratorBaseFamily : Prop :=
  H.card = 8 ∧
    projectsToT H ∧
    (∀ i : TightIndex, removable H (R i)) ∧
    (∀ i j : TightIndex, i ≠ j → ¬ removable H (R i ∪ R j))

def P (x : Coordinate) : Family :=
  H ∪ (X.erase x).powerset

def hStable (F : Family) : Prop :=
  ∀ A ∈ H, ∀ B ∈ F, A ∪ B ∈ F

def frequency (F : Family) (x : Coordinate) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

def coefficient (F : Family) (x : Coordinate) : ℤ :=
  (2 : ℤ) * frequency F x - F.card

def coefficientVector (F : Family) : Coordinate → ℤ :=
  coefficient F

def baseRow : Coordinate → ℤ :=
  fun x => if x.val < 3 then 0 else 6

def tightRow (i : TightIndex) : Coordinate → ℤ :=
  fun x => if x = t i then -28 else if x.val < 3 then 0 else 4

def outsideRow (i : TightIndex) : Coordinate → ℤ :=
  fun x => if x = z i then -25 else if x.val < 3 then 1 else 7

def puncturedStableFibersAndCoefficientRows : Prop :=
  (∀ x : Coordinate, unionClosed (P x) ∧ hStable (P x)) ∧
    coefficientVector H = baseRow ∧
    (∀ i : TightIndex, coefficientVector (P (t i)) = tightRow i) ∧
    (∀ i : TightIndex, coefficientVector (P (z i)) = outsideRow i)

def W : WeightedFamily :=
  H.1 +
    (P (t 0)).1 +
    (P (t 1)).1 +
    (P (t 2)).1 +
    13 • (P (z 0)).1 +
    7 • (P (z 1)).1 +
    7 • (P (z 2)).1

def weightedFrequency (M : WeightedFamily) (x : Coordinate) : ℕ :=
  (M.map (fun A => if x ∈ A then 1 else 0)).sum

def weightedCoefficient (M : WeightedFamily) (x : Coordinate) : ℤ :=
  (2 : ℤ) * weightedFrequency M x - M.card

def exactBalancedWeightedFiberCounterfeit : Prop :=
  W.card = 1169 ∧
    (∀ i : TightIndex, weightedFrequency W (t i) = 584) ∧
    weightedFrequency W (z 0) = 480 ∧
    weightedFrequency W (z 1) = 576 ∧
    weightedFrequency W (z 2) = 576 ∧
    (∀ i : TightIndex, weightedCoefficient W (t i) = -1) ∧
    weightedCoefficient W (z 0) = -209 ∧
    weightedCoefficient W (z 1) = -17 ∧
    weightedCoefficient W (z 2) = -17 ∧
    unionClosed H ∧
    hStable H ∧
    (∀ x : Coordinate, unionClosed (P x) ∧ hStable (P x))

end MathlibPlus.Open.ResearchFormalization.Batch0315
