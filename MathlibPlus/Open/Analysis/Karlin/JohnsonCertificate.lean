import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.Karlin

abbrev JohnsonSubset (k : ℕ) := {S : Finset (Fin 12) // S.card = k}
abbrev JohnsonPair := JohnsonSubset 2
abbrev JohnsonTriple := JohnsonSubset 3
abbrev JohnsonFour := JohnsonSubset 4
abbrev JohnsonFive := JohnsonSubset 5
abbrev JohnsonSix := JohnsonSubset 6

/-- The intersection size on the three-subset carrier. -/
def johnsonOverlap (S T : JohnsonTriple) : ℕ :=
  (S.1 ∩ T.1).card

/-- The four intersection values of the Johnson quadratic-form matrix. -/
def johnsonK : Matrix JohnsonTriple JohnsonTriple ℝ :=
  fun S T =>
    if johnsonOverlap S T = 3 then 9
    else if johnsonOverlap S T = 2 then -1
    else if johnsonOverlap S T = 1 then 1
    else 3

/-- The projection part and the entrywise nonnegative remainder. -/
def johnsonL : Matrix JohnsonTriple JohnsonTriple ℝ :=
  fun S T =>
    if johnsonOverlap S T = 3 then 9
    else if johnsonOverlap S T = 2 then -1
    else if johnsonOverlap S T = 1 then 1 / 4
    else -3 / 28

def johnsonR : Matrix JohnsonTriple JohnsonTriple ℝ :=
  fun S T =>
    if johnsonOverlap S T = 3 then 0
    else if johnsonOverlap S T = 2 then 0
    else if johnsonOverlap S T = 1 then 3 / 4
    else 87 / 28

/-- Pair-versus-triple incidence, with rows indexed by pairs. -/
def johnsonB : Matrix JohnsonPair JohnsonTriple ℝ :=
  fun A S => if A.1 ⊆ S.1 then 1 else 0

def johnsonM : Matrix JohnsonTriple JohnsonTriple ℝ :=
  Matrix.transpose johnsonB * johnsonB

def johnsonVector (y : Fin 12 → ℝ) : JohnsonTriple → ℝ :=
  fun S => ∏ i ∈ S.1, y i

/-- Coordinate-order zero padding into the twelve-variable carrier. -/
def johnsonZeroPad (n : ℕ) (_hn : n ≤ 12) (y : Fin n → ℝ) : Fin 12 → ℝ :=
  fun i => if hi : i.val < n then y ⟨i.val, hi⟩ else 0

/-- The four monomial-symmetric sums in the even part of the source Q. -/
def johnsonQ222 (y : Fin 12 → ℝ) : ℝ :=
  ∑ S : JohnsonTriple, ∏ i ∈ S.1, y i ^ 2

def johnsonQ2211 (y : Fin 12 → ℝ) : ℝ :=
  ∑ U : JohnsonFour,
    ∑ A : JohnsonPair,
      if A.1 ⊆ U.1 then
        (∏ i ∈ A.1, y i ^ 2) * (∏ i ∈ U.1 \ A.1, y i)
      else 0

def johnsonQ21111 (y : Fin 12 → ℝ) : ℝ :=
  ∑ U : JohnsonFive,
    ∑ i ∈ U.1, y i ^ 2 * ∏ j ∈ U.1.erase i, y j

def johnsonQ111111 (y : Fin 12 → ℝ) : ℝ :=
  ∑ U : JohnsonSix, ∏ i ∈ U.1, y i

/-- Q from the even-exponent part of the source, with its four coefficients. -/
def johnsonQ (y : Fin 12 → ℝ) : ℝ :=
  9 * johnsonQ222 y - 2 * johnsonQ2211 y +
    6 * johnsonQ21111 y + 60 * johnsonQ111111 y

/-- The ordered-pair multiplicities for intersection sizes 3,2,1,0. -/
def johnsonOrderedPairMultiplicities : Fin 4 → ℕ :=
  ![1, 2, 6, 20]

/-- Claim 678: the padded twelve-variable Johnson quadratic form identity. -/
def johnsonQuadraticFormIdentity : Prop :=
  johnsonOrderedPairMultiplicities = ![1, 2, 6, 20] ∧
    ∀ (n : ℕ) (hn : n ≤ 12) (y : Fin n → ℝ),
      johnsonQ (johnsonZeroPad n hn y) =
        ∑ S : JohnsonTriple, ∑ T : JohnsonTriple,
          johnsonVector (johnsonZeroPad n hn y) S * johnsonK S T *
            johnsonVector (johnsonZeroPad n hn y) T

/-- Claim 679: the exact Johnson decomposition, spectral relation, and PSD
statement for the matrix L. -/
def positiveSemidefiniteJohnsonDecomposition : Prop :=
  (∀ S T : JohnsonTriple, johnsonL S T = johnsonL T S) ∧
    johnsonK = johnsonL + johnsonR ∧
    (∀ S T : JohnsonTriple, 0 ≤ johnsonR S T) ∧
    johnsonL * johnsonL = (90 / 7 : ℝ) • johnsonL ∧
    (∀ μ : ℝ,
      (∃ v : JohnsonTriple → ℝ, v ≠ 0 ∧
        ∀ S : JohnsonTriple,
          (∑ T : JohnsonTriple, johnsonL S T * v T) = μ * v S) →
      μ = 0 ∨ μ = 90 / 7) ∧
    ∀ v : JohnsonTriple → ℝ,
      0 ≤ ∑ S : JohnsonTriple,
        v S * ∑ T : JohnsonTriple, johnsonL S T * v T

/-- Application of a matrix to a column vector in the source's convention. -/
def johnsonApply (L : Matrix JohnsonTriple JohnsonTriple ℝ)
    (v : JohnsonTriple → ℝ) : JohnsonTriple → ℝ :=
  fun S => ∑ T : JohnsonTriple, L S T * v T

def johnsonPairIncidenceSubmodule : Submodule ℝ (JohnsonTriple → ℝ) :=
  Submodule.span ℝ (Set.range (fun A : JohnsonPair =>
    fun S : JohnsonTriple => if A.1 ⊆ S.1 then 1 else 0))

def johnsonBasisVector (T : JohnsonTriple) : JohnsonTriple → ℝ :=
  fun S => if S = T then 1 else 0

/-- Claim 680: pair-incidence annihilation and the shifted-basis mechanism. -/
def pairIncidenceAnnihilationMechanism : Prop :=
  (∀ v : JohnsonTriple → ℝ,
      v ∈ johnsonPairIncidenceSubmodule → johnsonApply johnsonL v = 0) ∧
    (∀ T : JohnsonTriple,
      johnsonApply johnsonL (johnsonBasisVector T) -
          (90 / 7 : ℝ) • johnsonBasisVector T ∈
        johnsonPairIncidenceSubmodule) ∧
    johnsonL * johnsonL = (90 / 7 : ℝ) • johnsonL

/-- Claim 681: the incidence polynomial and scaled projection identities. -/
def scaledIncidenceMatrixIdentities : Prop :=
  let B : Matrix JohnsonPair JohnsonTriple ℝ := johnsonB
  let M : Matrix JohnsonTriple JohnsonTriple ℝ := Matrix.transpose B * B
  let I : Matrix JohnsonTriple JohnsonTriple ℝ := 1
  let A : Matrix JohnsonTriple JohnsonTriple ℝ := (28 : ℝ) • johnsonL
  M * (M - (8 : ℝ) • I) * (M - (18 : ℝ) • I) *
        (M - (30 : ℝ) • I) = 0 ∧
    (12 : ℝ) • ((28 : ℝ) • johnsonL) =
      ((8 : ℝ) • I - M) * ((18 : ℝ) • I - M) *
        ((30 : ℝ) • I - M) ∧
    A * A = (360 : ℝ) • A

end MathlibPlus.Open.Analysis.Karlin
