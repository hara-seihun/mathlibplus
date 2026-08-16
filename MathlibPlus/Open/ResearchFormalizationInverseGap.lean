import MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386
import MathlibPlus.Open.Analysis.NormInheritance

open scoped BigOperators
open Filter
open Set

namespace MathlibPlus.Open.ResearchFormalizationInverseGap

noncomputable section

/-- A complete orthonormal eigenframe for a real symmetric matrix. -/
def orthonormalEigenframe {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalues : Fin (n + 1) → ℝ)
    (u : Fin (n + 1) → Fin (n + 1) → ℝ) : Prop :=
  (∀ j : Fin (n + 1), Q.mulVec (u j) = eigenvalues j • u j) ∧
    (∀ i j : Fin (n + 1),
      dotProduct (u i) (u j) = if i = j then 1 else 0) ∧
    (∀ v : Fin (n + 1) → ℝ,
      ∃ c : Fin (n + 1) → ℝ, v = ∑ j, c j • u j)

/-- Claim 14902: the adjugate has the rank-one spectral form in a complete
orthonormal eigenbasis, with the simple eigenvalue at index zero. -/
def claim14902 : Prop :=
  ∀ (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalues : Fin (n + 1) → ℝ)
    (u : Fin (n + 1) → Fin (n + 1) → ℝ),
    Q = Q.transpose →
    orthonormalEigenframe Q eigenvalues u →
    MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.simpleEigenvalue
      Q (eigenvalues 0) (u 0) →
    Matrix.adjugate
        (MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.spectralShift Q (eigenvalues 0)) =
      (∏ j ∈ (Finset.univ.erase (0 : Fin (n + 1))),
        (eigenvalues j - eigenvalues 0)) •
        (fun i j => u 0 i * u 0 j)

def hostileMatrix (ε t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.matrix2x2 0 t t ε

def hostileLowestEigenvalue (ε t : ℝ) : ℝ :=
  (ε - Real.sqrt (ε ^ 2 + 4 * t ^ 2)) / 2

/-- The first-coordinate-normalized lowest eigenvector displayed in the source. -/
def hostileNormalizedLowestEigenvector (ε t : ℝ) : Fin 2 → ℝ :=
  fun i =>
    if i = 0 then 1
    else -2 * t / (ε + Real.sqrt (ε ^ 2 + 4 * t ^ 2))

def hostileNormalizedEigenvectorFunctional (ε t : ℝ) : ℝ :=
  hostileNormalizedLowestEigenvector ε t 1

/-- Claim 14913: the hostile family has perturbation norm `|t|` in the
Euclidean operator norm, while its normalized eigenvector functional has the
reciprocal-gap derivative. -/
def claim14913 : Prop :=
  (∀ ε t : ℝ,
    MathlibPlus.Open.Analysis.spectralNorm
        (hostileMatrix ε t - hostileMatrix ε 0) = |t|) ∧
    (∀ ε : ℝ, 0 < ε →
      |deriv (fun t : ℝ => hostileNormalizedEigenvectorFunctional ε t) 0| =
        1 / ε)

def sourceEventMatrix (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  if i = 0 then
    MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.bandOneMatrix (1 / 2)
  else if i = 1 then
    MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.bandOneMatrix 1
  else
    MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.bandOneMatrix (1 / 4)

def sourceWeights (ε t : ℝ) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then
      (-ε - (Real.pi * t / Real.sqrt 2) *
        ((1 : ℝ) / 2 - 1 / Real.pi)) / 2
    else if i = 1 then
      (ε - (Real.pi * t / Real.sqrt 2) *
        ((1 : ℝ) / 2 + 1 / Real.pi)) / 4
    else
      Real.pi * t / Real.sqrt 2

def signedSourceMatrix (w : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ i : Fin 3, w i • sourceEventMatrix i

def hostileFirstCoordinate : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else 0

def hostileSecondCoordinate : Fin 2 → ℝ :=
  fun i => if i = 1 then 1 else 0

/-- The bordered-determinant functional for the normalized lowest eigenvector. -/
def hostileBorderedFunctional (ε t : ℝ) : ℝ :=
  let B (a : Fin 2 → ℝ) :=
    Matrix.det
      (MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.borderedMatrix
        (hostileMatrix ε t) (hostileLowestEigenvalue ε t)
        hostileFirstCoordinate a)
  B hostileSecondCoordinate / B hostileFirstCoordinate

/-- Claim 14914: the exact three fixed source events realize the hostile
family with affine signed weights, and the resulting finite-coordinate motion
has the reciprocal-gap bordered-determinant sensitivity. -/
def claim14914 : Prop :=
  (∀ ε t : ℝ,
    signedSourceMatrix (sourceWeights ε t) = hostileMatrix ε t) ∧
  (∀ i : Fin 3, ∃ a b c : ℝ,
    ∀ ε t : ℝ, sourceWeights ε t i = a * ε + b * t + c) ∧
  (∀ i : Fin 3, ∀ ε t : ℝ,
    sourceWeights ε t i - sourceWeights ε 0 i =
      t * (sourceWeights 0 1 i - sourceWeights 0 0 i)) ∧
  (∀ ε : ℝ, 0 < ε →
    (∀ t : ℝ,
      hostileBorderedFunctional ε t =
        hostileNormalizedEigenvectorFunctional ε t) ∧
    |deriv (fun t : ℝ => hostileBorderedFunctional ε t) 0| = 1 / ε)

end
end MathlibPlus.Open.ResearchFormalizationInverseGap
