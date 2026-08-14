import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Research.Rosser

def rosserStopping (y : ℝ) (l : List ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → 2 * j ≤ l.length →
    ((l.take (2 * j - 1)).prod : ℝ) *
        (l.getD (2 * j - 1) 0 : ℝ) ^ 3 < y

def rosserAdmissible (y : ℝ) (l : List ℕ) : Prop :=
  List.Pairwise (fun p q : ℕ => p > q) l ∧
    (∀ p ∈ l, Nat.Prime p ∧ (p : ℝ) < Real.sqrt y) ∧
    rosserStopping y l

def lowerCubicRosserSupport (y : ℝ) : Set ℕ :=
  {d | ∃ l : List ℕ, rosserAdmissible y l ∧ d = l.prod}

def claim36757 : Prop :=
  ∀ y : ℝ, 1 < y →
    (∀ d ∈ lowerCubicRosserSupport y, Squarefree d) ∧
    (∀ d, d ∈ lowerCubicRosserSupport y ↔
      ∃ l : List ℕ, rosserAdmissible y l ∧ d = l.prod)

def ratioThreeUpper (y : ℝ) (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (Real.log y / (2 * (3 : ℝ) ^ j))

def ratioThreeEndpointExponent (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) +
    Finset.sum (Finset.range (j - 1)) (fun h => (1 / 3 : ℝ) ^ (h + 1)) +
    3 / (2 * (3 : ℝ) ^ j)

def geometricBoxChoice (y : ℝ) (r : ℕ) (l : List ℕ) : Prop :=
  l.length = 2 * r + 1 ∧
    List.Pairwise (fun p q : ℕ => p > q) l ∧
    Nat.Prime (l.getD 0 0) ∧
    Real.sqrt y / 4 < (l.getD 0 0 : ℝ) ∧
    (l.getD 0 0 : ℝ) ≤ Real.sqrt y / 2 ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ r →
      let p := l.getD (2 * j - 1) 0
      let q := l.getD (2 * j) 0
      Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
        ratioThreeUpper y j / 2 < (p : ℝ) ∧
        (p : ℝ) ≤ ratioThreeUpper y j ∧
        ratioThreeUpper y j / 2 < (q : ℝ) ∧
        (q : ℝ) ≤ ratioThreeUpper y j)

def geometricBoxSupport (y : ℝ) (r : ℕ) : Set ℕ :=
  {d | ∃ l : List ℕ, geometricBoxChoice y r l ∧ d = l.prod}

def ratioThreeEndpointIdentity : Prop :=
  ∀ j : ℕ, 1 ≤ j → ratioThreeEndpointExponent j = 1

def ratioThreeIntervalsDecrease (y : ℝ) (r : ℕ) : Prop :=
  ∀ j k : ℕ, j < k → k ≤ r → ratioThreeUpper y k < ratioThreeUpper y j

def claim36758 : Prop :=
  ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
    let L := Real.log y
    let ell := Real.log L
    let r := ⌊Real.log (L / ell ^ 2) / Real.log 3⌋₊
    ratioThreeEndpointIdentity ∧
      ratioThreeIntervalsDecrease y r ∧
      (∀ l, geometricBoxChoice y r l → l.prod ∈ lowerCubicRosserSupport y) ∧
      ((geometricBoxSupport y r).ncard : ℝ) ≥
        y * Real.exp (-4 * ell ^ 2)

def singlePathBoxChoice (y : ℝ) (r : ℕ) (l : List ℕ) : Prop :=
  l.length = 2 * r + 1 ∧
    List.Pairwise (fun p q : ℕ => p > q) l ∧
    Nat.Prime (l.getD 0 0) ∧
    ratioThreeUpper y 0 / 2 < (l.getD 0 0 : ℝ) ∧
    (l.getD 0 0 : ℝ) ≤ ratioThreeUpper y 0 ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ r →
      let p := l.getD (2 * j - 1) 0
      let q := l.getD (2 * j) 0
      Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
        ratioThreeUpper y j / 2 < (p : ℝ) ∧
        (p : ℝ) ≤ ratioThreeUpper y j ∧
        ratioThreeUpper y j / 2 < (q : ℝ) ∧
        (q : ℝ) ≤ ratioThreeUpper y j)

def singlePathBoxSupport (y : ℝ) (r : ℕ) : Set ℕ :=
  {d | ∃ l : List ℕ, singlePathBoxChoice y r l ∧ d = l.prod}

def claim36759 : Prop :=
  ∀ y : ℝ, 1 < y → ∀ r : ℕ,
    singlePathBoxSupport y r ⊆ lowerCubicRosserSupport y

def logLength (y : ℝ) : ℝ := Real.log y

def logLogLength (y : ℝ) : ℝ := Real.log (logLength y)

def logThree : ℝ := Real.log 3

def ratioThreeQ (y : ℝ) (r : ℕ) : ℝ :=
  logLength y / (3 : ℝ) ^ r

def ratioThreeS (y : ℝ) (r : ℕ) : ℝ := Real.log (ratioThreeQ y r)

def boxLogCard (y : ℝ) (r : ℕ) : ℝ :=
  Real.log ((singlePathBoxSupport y r).ncard : ℝ)

def boxLogMain (y : ℝ) (r : ℕ) : ℝ :=
  Real.log (ratioThreeUpper y 0) +
    2 * Finset.sum (Finset.range r) (fun j => Real.log (ratioThreeUpper y (j + 1))) -
    Real.log (Real.log (ratioThreeUpper y 0)) -
    2 * Finset.sum (Finset.range r) (fun j =>
      Real.log (Real.log (ratioThreeUpper y (j + 1))))

def boxNumeratorExact (y : ℝ) (r : ℕ) : ℝ :=
  Real.log (ratioThreeUpper y 0) +
    2 * Finset.sum (Finset.range r) (fun j => Real.log (ratioThreeUpper y (j + 1)))

def boxNumeratorApprox (y : ℝ) (r : ℕ) : ℝ :=
  logLength y - ratioThreeQ y r / 2 -
    (2 * (r : ℝ) + 1) * Real.log 2

def boxDenominatorExact (y : ℝ) (r : ℕ) : ℝ :=
  Real.log (Real.log (ratioThreeUpper y 0)) +
    2 * Finset.sum (Finset.range r) (fun j =>
      Real.log (Real.log (ratioThreeUpper y (j + 1))))

def boxDenominatorApprox (y : ℝ) (r : ℕ) : ℝ :=
  (2 * (r : ℝ) + 1) * (logLogLength y - Real.log 2) -
    logThree * (r : ℝ) * ((r : ℝ) + 1)

def ratioThreePhi (s : ℝ) : ℝ :=
  Real.exp s / 2 - s ^ 2 / logThree + s

def IsBigOAtInfinity (f g : ℝ → ℝ) : Prop :=
  ∃ C T : ℝ, 0 ≤ C ∧ ∀ y : ℝ, T ≤ y → |f y| ≤ C * |g y|

def IsLittleOAtInfinity (f g : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ y : ℝ, T ≤ y → |f y| ≤ ε * |g y|

def boxLogExpansion : Prop :=
  ∃ C T : ℝ, 0 ≤ C ∧
    ∀ y : ℝ, T ≤ y → ∀ r : ℕ,
      (singlePathBoxSupport y r).Nonempty →
      |boxLogCard y r - boxLogMain y r| ≤ C * (r + 1)

def boxNumeratorIdentity : Prop :=
  ∃ T : ℝ, ∀ y : ℝ, T ≤ y → ∀ r : ℕ,
    boxNumeratorExact y r = boxNumeratorApprox y r

def boxDenominatorExpansion : Prop :=
  ∃ C T : ℝ, 0 ≤ C ∧
    ∀ y : ℝ, T ≤ y → ∀ r : ℕ,
      (singlePathBoxSupport y r).Nonempty →
      |boxDenominatorExact y r - boxDenominatorApprox y r| ≤ C

def boxGapExpansion : Prop :=
  ∃ C T : ℝ, 0 ≤ C ∧
    ∀ y : ℝ, T ≤ y → ∀ r : ℕ,
      (singlePathBoxSupport y r).Nonempty →
      |logLength y - boxLogCard y r -
          (logLogLength y ^ 2 / logThree +
            ratioThreePhi (ratioThreeS y r))| ≤ C * (logLogLength y + 1)

def ratioThreePhiLowerBound : Prop :=
  ∃ K : ℝ, ∀ s : ℝ, 0 ≤ s → K ≤ ratioThreePhi s

def ratioThreeExpCubicBound : Prop :=
  ∃ S : ℝ, ∀ s : ℝ, S ≤ s → Real.exp s / 2 ≥ s ^ 3 / 12

def boxUniformUpperBound : Prop :=
  ∃ C T : ℝ, 0 ≤ C ∧
    ∀ y : ℝ, T ≤ y → ∀ r : ℕ,
      (singlePathBoxSupport y r).Nonempty →
      boxLogCard y r ≤
        logLength y - logLogLength y ^ 2 / logThree + C * (logLogLength y + 1)

def claim36760 : Prop :=
  boxLogExpansion ∧ boxNumeratorIdentity ∧ boxDenominatorExpansion ∧
    boxGapExpansion ∧ ratioThreePhiLowerBound ∧ ratioThreeExpCubicBound ∧
    boxUniformUpperBound

def optimizedDepth (y : ℝ) : ℕ :=
  ⌊Real.log (logLength y / logLogLength y) / Real.log 3⌋₊

def optimizedQ (y : ℝ) : ℝ := ratioThreeQ y (optimizedDepth y)
def optimizedS (y : ℝ) : ℝ := ratioThreeS y (optimizedDepth y)

def optimizedSubset : Prop :=
  ∃ T : ℝ, ∀ y : ℝ, T ≤ y →
    singlePathBoxSupport y (optimizedDepth y) ⊆ lowerCubicRosserSupport y

def optimizedQSandwich : Prop :=
  ∃ T : ℝ, ∀ y : ℝ, T ≤ y →
    logLogLength y ≤ optimizedQ y ∧ optimizedQ y < 3 * logLogLength y

def optimizedLogAsymptotic : Prop :=
  IsBigOAtInfinity
    (fun y => boxLogCard y (optimizedDepth y) -
      (logLength y - logLogLength y ^ 2 / logThree))
    (fun y => logLogLength y + 1)

def optimizedSBound : Prop :=
  IsBigOAtInfinity optimizedS (fun y => Real.log (logLogLength y) + 1)

def optimizedQBound : Prop :=
  IsBigOAtInfinity (fun y => optimizedQ y / 2) (fun y => logLogLength y + 1)

def optimizedPhiBound : Prop :=
  IsBigOAtInfinity (fun y => ratioThreePhi (optimizedS y))
    (fun y => logLogLength y + 1)

def lowerSupportExpLowerBound : Prop :=
  ∃ C T : ℝ, 0 ≤ C ∧ ∀ y : ℝ, T ≤ y →
    y * Real.exp (-logLogLength y ^ 2 / logThree - C * (logLogLength y + 1)) ≤
      (lowerCubicRosserSupport y).ncard

def lowerSupportEpsilonBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ y : ℝ, T ≤ y →
    y * Real.exp (-(1 / logThree + ε) * logLogLength y ^ 2) ≤
      (lowerCubicRosserSupport y).ncard

def claim36761 : Prop :=
  optimizedSubset ∧ optimizedQSandwich ∧ optimizedLogAsymptotic ∧
    optimizedSBound ∧ optimizedQBound ∧ optimizedPhiBound ∧
    lowerSupportExpLowerBound ∧ lowerSupportEpsilonBound

def singlePathCounts (y : ℝ) : Set ℕ :=
  {m | ∃ r : ℕ, (singlePathBoxSupport y r).ncard = m}

noncomputable def maxSinglePathCount (y : ℝ) : ℕ :=
  sSup (singlePathCounts y)

def maxSinglePathWitness : Prop :=
  ∃ T : ℝ, ∀ y : ℝ, T ≤ y →
    ∃ r : ℕ,
      (singlePathBoxSupport y r).ncard = maxSinglePathCount y ∧
      ∀ r' : ℕ, (singlePathBoxSupport y r').ncard ≤ maxSinglePathCount y

def claim36762 : Prop :=
  maxSinglePathWitness ∧
    IsBigOAtInfinity
      (fun y => Real.log (maxSinglePathCount y) -
        (logLength y - logLogLength y ^ 2 / logThree))
      (fun y => logLogLength y + 1) ∧
    IsLittleOAtInfinity
      (fun y => (maxSinglePathCount y : ℝ))
      (fun y => y / Real.log y ^ 2) ∧
    ¬ ∃ c T : ℝ, 0 < c ∧ ∀ y : ℝ, T ≤ y →
      c * (y / Real.log y ^ 2) ≤ (maxSinglePathCount y : ℝ)

end MathlibPlus.Open.Research.Rosser
