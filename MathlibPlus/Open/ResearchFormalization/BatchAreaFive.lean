import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

inductive AreaFiveShape
  | five
  | fourOne
  | threeTwo
  | threeOneOne
  | twoTwoOne
  | twoOneOneOne
  | oneOneOneOneOne
  deriving DecidableEq, Repr

def areaFiveRow : AreaFiveShape → ℕ → List ℕ
  | .five, d => List.range (d - 1) ++ [d + 4]
  | .fourOne, d => List.range (d - 2) ++ [d - 1, d + 3]
  | .threeTwo, d => List.range (d - 2) ++ [d, d + 2]
  | .threeOneOne, d => List.range (d - 3) ++ [d - 2, d - 1, d + 2]
  | .twoTwoOne, d => List.range (d - 3) ++ [d - 2, d, d + 1]
  | .twoOneOneOne, d =>
      List.range (d - 4) ++ [d - 3, d - 2, d - 1, d + 1]
  | .oneOneOneOneOne, d =>
      List.range (d - 5) ++ [d - 4, d - 3, d - 2, d - 1, d]

def areaFiveMinimumDimension : AreaFiveShape → ℕ
  | .five => 5
  | .fourOne => 4
  | .threeTwo => 3
  | .threeOneOne => 3
  | .twoTwoOne => 3
  | .twoOneOneOne => 4
  | .oneOneOneOneOne => 5

def areaFiveAvailable (shape : AreaFiveShape) (d : ℕ) : Prop :=
  areaFiveMinimumDimension shape ≤ d

def areaFiveAvailableRows (d : ℕ) : List (List ℕ) :=
  (if areaFiveMinimumDimension .five ≤ d then [areaFiveRow .five d] else []) ++
    (if areaFiveMinimumDimension .fourOne ≤ d then [areaFiveRow .fourOne d] else []) ++
    (if areaFiveMinimumDimension .threeTwo ≤ d then [areaFiveRow .threeTwo d] else []) ++
    (if areaFiveMinimumDimension .threeOneOne ≤ d then [areaFiveRow .threeOneOne d] else []) ++
    (if areaFiveMinimumDimension .twoTwoOne ≤ d then [areaFiveRow .twoTwoOne d] else []) ++
    (if areaFiveMinimumDimension .twoOneOneOne ≤ d then [areaFiveRow .twoOneOneOne d] else []) ++
    (if areaFiveMinimumDimension .oneOneOneOneOne ≤ d then
        [areaFiveRow .oneOneOneOneOne d]
      else [])

/-- The seven area-five row sets and their availability counts in Claim 1256. -/
def area_five_shape_list_and_minimum_dimensions : Prop :=
  (∀ d : ℕ, 3 ≤ d →
      List.length (areaFiveAvailableRows d) =
        if d = 3 then 3 else if d = 4 then 5 else 7) ∧
    (areaFiveAvailableRows 3 =
      [ areaFiveRow .threeTwo 3,
        areaFiveRow .threeOneOne 3,
        areaFiveRow .twoTwoOne 3 ]) ∧
    (areaFiveAvailableRows 4 =
      [ areaFiveRow .fourOne 4,
        areaFiveRow .threeTwo 4,
        areaFiveRow .threeOneOne 4,
        areaFiveRow .twoTwoOne 4,
        areaFiveRow .twoOneOneOne 4 ]) ∧
    (∀ d : ℕ, 5 ≤ d →
      areaFiveAvailableRows d =
        [ areaFiveRow .five d,
          areaFiveRow .fourOne d,
          areaFiveRow .threeTwo d,
          areaFiveRow .threeOneOne d,
          areaFiveRow .twoTwoOne d,
          areaFiveRow .twoOneOneOne d,
          areaFiveRow .oneOneOneOneOne d ])

end MathlibPlus.Open.ResearchFormalization
