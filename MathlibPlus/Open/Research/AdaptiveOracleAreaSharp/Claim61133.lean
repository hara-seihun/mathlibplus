import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.AdaptiveOracleAreaSharp

noncomputable section

abbrev Coordinate61133 := Fin 83
abbrev SignState61133 := Coordinate61133 → Bool

def signValue61133 (s : Bool) : ℝ :=
  if s then 1 else -1

def uniformExpectation61133 (g : SignState61133 → ℝ) : ℝ :=
  (Fintype.card SignState61133 : ℝ)⁻¹ * ∑ x : SignState61133, g x

def q61133 : ℝ := 1 / (2 : ℝ) ^ 84

def p61133 : ℝ := 1 - q61133

def lastCoordinate61133 : Coordinate61133 := Fin.last 82

def parityFirst82_61133 (x : SignState61133) : ℝ :=
  ∏ i : Coordinate61133,
    if i.val < 82 then signValue61133 (x i) else 1

def target61133 (x : SignState61133) : ℝ :=
  p61133 * signValue61133 (x lastCoordinate61133) +
    q61133 * parityFirst82_61133 x

def replaceSign61133 (x : SignState61133) (i : Coordinate61133)
    (s : Bool) : SignState61133 :=
  Function.update x i s

def differenceOperator61133 (i : Coordinate61133)
    (g : SignState61133 → ℝ) : SignState61133 → ℝ :=
  fun x =>
    (g (replaceSign61133 x i true) - g (replaceSign61133 x i false)) / 2

def mixedDifference61133 (U : Finset Coordinate61133) :
    SignState61133 → ℝ :=
  U.toList.foldl (fun g i => differenceOperator61133 i g) target61133

def h61133 (U : Finset Coordinate61133) : ℝ :=
  uniformExpectation61133 (fun x => |mixedDifference61133 U x|)

def allSubsets61133 : Finset (Finset Coordinate61133) :=
  (Finset.univ : Finset Coordinate61133).powerset

def H61133 : ℝ :=
  Finset.sum allSubsets61133 h61133

def L61133 (i : Coordinate61133) : ℝ :=
  Finset.sum allSubsets61133 (fun U => if i ∈ U then h61133 U else 0)

def S61133 : ℝ :=
  ∑ i : Coordinate61133, L61133 i

def Q61133 : ℝ :=
  ∑ i : Coordinate61133, (L61133 i) ^ 2

def variance61133 : ℝ :=
  uniformExpectation61133
    (fun x => (target61133 x - uniformExpectation61133 target61133) ^ 2)

def normalizedRatio61133 : ℝ :=
  ((1 + H61133) * S61133 * variance61133) / Q61133

def limitingRatio61133 : ℝ :=
  ((13 / 4 : ℝ) * (45 / 4 : ℝ) * (1 : ℝ)) /
    (1 + 41 / 32 : ℝ)

/-- Claim 61133: the explicit 83-coordinate Rademacher counterexample to the
marked mixed-difference inequality, with the fixed exact dyadic parameter. -/
def claim61133 : Prop :=
  (∀ x : SignState61133, |target61133 x| ≤ 1) ∧
    H61133 = 9 / 4 - 3 * q61133 ∧
    L61133 lastCoordinate61133 = p61133 ∧
    (∀ i : Coordinate61133, i.val < 82 → L61133 i = 1 / 8) ∧
    S61133 = 45 / 4 - q61133 ∧
    Q61133 = p61133 ^ 2 + 41 / 32 ∧
    variance61133 = p61133 ^ 2 + q61133 ^ 2 ∧
    normalizedRatio61133 =
      ((13 / 4 : ℝ) - 3 * q61133) *
        ((45 / 4 : ℝ) - q61133) *
        (p61133 ^ 2 + q61133 ^ 2) /
          (p61133 ^ 2 + 41 / 32) ∧
    normalizedRatio61133 > 16 ∧
    ¬ ((1 + H61133) * S61133 * variance61133 ≤ 16 * Q61133) ∧
    limitingRatio61133 = 1170 / 73 ∧
    (1170 / 73 : ℝ) > 16

end

end MathlibPlus.Open.Research.AdaptiveOracleAreaSharp
