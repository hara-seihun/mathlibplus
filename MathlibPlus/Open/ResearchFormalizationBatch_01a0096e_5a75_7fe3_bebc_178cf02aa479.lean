import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open
namespace ResearchFormalizationBatch_01a0096e_5a75_7fe3_bebc_178cf02aa479

noncomputable section

abbrev FourIndex := Fin 2 × Fin 2

/-- The two-dimensional identity matrix used in the gauged Bell realization. -/
def identityTwo : Matrix (Fin 2) (Fin 2) ℂ := 1

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1
  else if i = 1 ∧ j = 0 then 1
  else 0

def pauliY : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then -Complex.I
  else if i = 1 ∧ j = 0 then Complex.I
  else 0

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = j then if i = 0 then 1 else -1 else 0

def identityFour : Matrix FourIndex FourIndex ℂ := 1

def dMatrix : Matrix FourIndex FourIndex ℂ :=
  Matrix.kronecker pauliZ identityTwo

def jMatrix : Matrix FourIndex FourIndex ℂ :=
  Matrix.kronecker identityTwo pauliY

def nMatrix : Matrix FourIndex FourIndex ℂ := dMatrix * jMatrix

def rhMatrix : Matrix FourIndex FourIndex ℂ :=
  Matrix.kronecker pauliZ pauliX

def rcMatrix : Matrix FourIndex FourIndex ℂ :=
  Matrix.kronecker identityTwo pauliX

def rhoOf (x g : ℝ) : ℝ := g / (2 + x)

def arthurFactor (x : ℝ) : Matrix FourIndex FourIndex ℂ :=
  (((2 + x : ℝ) : ℂ) / 4) • identityFour - (1 / 2 : ℂ) • dMatrix

def relativeFactor (rho : ℝ) : Matrix FourIndex FourIndex ℂ :=
  identityFour - (rho : ℂ) • jMatrix

def qStar (x g : ℝ) : Matrix FourIndex FourIndex ℂ :=
  arthurFactor x * relativeFactor (rhoOf x g)

def qStarAt (x rho : ℝ) : Matrix FourIndex FourIndex ℂ :=
  arthurFactor x * relativeFactor rho

def matrixSpectrum {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Set ℂ :=
  {z | ¬ Function.Bijective (fun v : ι → ℂ =>
    Matrix.mulVec (z • (1 : Matrix ι ι ℂ) - A) v)}

def arthurProfile (x : ℝ) : Fin 4 → ℂ := fun i =>
  if i.val < 2 then (x : ℂ) / 4 else ((4 + x : ℝ) : ℂ) / 4

def relativeProfile (rho : ℝ) : Fin 4 → ℂ := fun i =>
  if i.val < 2 then 1 - (rho : ℂ) else 1 + (rho : ℂ)

def jointProfile (x rho : ℝ) : Fin 4 → ℂ := fun i =>
  if i.val = 0 then ((x : ℂ) / 4) * (1 - (rho : ℂ))
  else if i.val = 1 then ((x : ℂ) / 4) * (1 + (rho : ℂ))
  else if i.val = 2 then (((4 + x : ℝ) : ℂ) / 4) * (1 - (rho : ℂ))
  else (((4 + x : ℝ) : ℂ) / 4) * (1 + (rho : ℂ))

def hasSpectrumProfile (A : Matrix FourIndex FourIndex ℂ)
    (profile : Fin 4 → ℂ) : Prop :=
  (∀ z : ℂ,
      Matrix.det (z • (1 : Matrix FourIndex FourIndex ℂ) - A) =
        ∏ i : Fin 4, (z - profile i)) ∧
    matrixSpectrum A = Set.range profile

def pairwiseProductSpectrum (x rho : ℝ) : Set ℂ :=
  {z |
    z = ((x : ℂ) / 4) * (1 - (rho : ℂ)) ∨
    z = ((x : ℂ) / 4) * (1 + (rho : ℂ)) ∨
    z = (((4 + x : ℝ) : ℂ) / 4) * (1 - (rho : ℂ)) ∨
    z = (((4 + x : ℝ) : ℂ) / 4) * (1 + (rho : ℂ))}

def quadraticReal (A : Matrix FourIndex FourIndex ℂ)
    (v : FourIndex → ℂ) : ℝ :=
  Complex.re (∑ i, star (v i) * (Matrix.mulVec A v) i)

def positiveSemidefinite (A : Matrix FourIndex FourIndex ℂ) : Prop :=
  Matrix.IsHermitian A ∧ ∀ v : FourIndex → ℂ, 0 ≤ quadraticReal A v

def claim13666_spectrumPositivityCriterion : Prop :=
  ∀ x g : ℝ,
    let rho := rhoOf x g
    hasSpectrumProfile (arthurFactor x) (arthurProfile x) ∧
    hasSpectrumProfile (relativeFactor rho) (relativeProfile rho) ∧
    hasSpectrumProfile (qStar x g) (jointProfile x rho) ∧
    matrixSpectrum (qStar x g) = pairwiseProductSpectrum x rho ∧
    (0 ≤ x →
      (positiveSemidefinite (qStar x g) ↔ |rho| ≤ 1) ∧
      (|rho| ≤ 1 ↔ |g| ≤ 2 + x))

def heatOperator (lambda : ℝ) (A : Matrix FourIndex FourIndex ℂ) :
    Matrix FourIndex FourIndex ℂ :=
  (((1 + lambda : ℝ) : ℂ) / 4) •
      (A + dMatrix * A * dMatrix) +
    (((1 - lambda : ℝ) : ℂ) / 4) •
      (rhMatrix * A * rhMatrix + rcMatrix * A * rcMatrix)

def claim13668_relativeWeylHeatCovariance : Prop :=
  ∀ (lambda x rho : ℝ),
    heatOperator lambda identityFour = identityFour ∧
    heatOperator lambda dMatrix = dMatrix ∧
    heatOperator lambda jMatrix = (lambda : ℂ) • jMatrix ∧
    heatOperator lambda nMatrix = (lambda : ℂ) • nMatrix ∧
    heatOperator lambda (qStarAt x rho) = qStarAt x (lambda * rho)

abbrev VCoordinate (k : ℕ) := Fin (k + 1) → ℂ

def reverseIndex (k : ℕ) (r : Fin (k + 1)) : Fin (k + 1) :=
  ⟨k - r.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

def weightVector (k : ℕ) (r : Fin (k + 1)) : VCoordinate k := fun s =>
  if s = r then 1 else 0

def signedWeylMatrix (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun r s => if r = reverseIndex k s then (-1 : ℂ) ^ s.val else 0

def normalizedSignedWeylMatrix (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  (Complex.I⁻¹ ^ k) • signedWeylMatrix k

def degreeGaugeMatrix (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun r s => if r = s then Complex.I ^ r.val else 0

def inverseDegreeGaugeMatrix (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun r s => if r = s then Complex.I⁻¹ ^ r.val else 0

def unsignedWeylMatrix (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun r s => if r = reverseIndex k s then 1 else 0

def claim13675_degreeDependentInvolutiveWeylGauge : Prop :=
  ∀ k : ℕ,
    (∀ r : Fin (k + 1),
      Matrix.mulVec (signedWeylMatrix k) (weightVector k r) =
        ((-1 : ℂ) ^ r.val) • weightVector k (reverseIndex k r)) ∧
    signedWeylMatrix k * signedWeylMatrix k =
      ((-1 : ℂ) ^ k) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) ∧
    normalizedSignedWeylMatrix k =
      (Complex.I⁻¹ ^ k) • signedWeylMatrix k ∧
    degreeGaugeMatrix k * normalizedSignedWeylMatrix k * inverseDegreeGaugeMatrix k =
      unsignedWeylMatrix k ∧
    (∀ r : Fin (k + 1),
      Matrix.mulVec (unsignedWeylMatrix k) (weightVector k r) =
        weightVector k (reverseIndex k r)) ∧
    unsignedWeylMatrix k * unsignedWeylMatrix k =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

def MCoordinate (k : ℕ) := (Fin (k + 1) × Fin (k + 1)) → ℂ

def swapMatrix (k : ℕ) : Matrix (Fin (k + 1) × Fin (k + 1))
    (Fin (k + 1) × Fin (k + 1)) ℂ := fun r s =>
  if r.1 = s.2 ∧ r.2 = s.1 then 1 else 0

def rhMatrixAt (k : ℕ) : Matrix (Fin (k + 1) × Fin (k + 1))
    (Fin (k + 1) × Fin (k + 1)) ℂ :=
  Matrix.kronecker (unsignedWeylMatrix k) (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

def rcMatrixAt (k : ℕ) : Matrix (Fin (k + 1) × Fin (k + 1))
    (Fin (k + 1) × Fin (k + 1)) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (unsignedWeylMatrix k)

def exactOrderFour {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Prop :=
  A ^ 4 = (1 : Matrix ι ι ℂ) ∧ A ^ 2 ≠ (1 : Matrix ι ι ℂ)

def generatedMatrixMonoid (k : ℕ) : Submonoid
    (Matrix (Fin (k + 1) × Fin (k + 1))
      (Fin (k + 1) × Fin (k + 1)) ℂ) :=
  Submonoid.closure {swapMatrix k, rhMatrixAt k}

def dihedralEightClosure (k : ℕ) : Prop :=
  Nonempty (generatedMatrixMonoid k ≃* DihedralGroup 4)

def claim13676_objectwiseD8Action : Prop :=
  ∀ k : ℕ,
    swapMatrix k * rhMatrixAt k * swapMatrix k = rcMatrixAt k ∧
    (swapMatrix k * rhMatrixAt k) ^ 2 = rhMatrixAt k * rcMatrixAt k ∧
    (swapMatrix k * rhMatrixAt k) ^ 4 =
      (1 : Matrix (Fin (k + 1) × Fin (k + 1))
        (Fin (k + 1) × Fin (k + 1)) ℂ) ∧
    (0 < k →
      exactOrderFour (swapMatrix k * rhMatrixAt k) ∧
      dihedralEightClosure k ∧
      (∀ B : generatedMatrixMonoid k,
        (rhMatrixAt k * rcMatrixAt k) * (B : Matrix (Fin (k + 1) × Fin (k + 1))
          (Fin (k + 1) × Fin (k + 1)) ℂ) =
        (B : Matrix (Fin (k + 1) × Fin (k + 1))
          (Fin (k + 1) × Fin (k + 1)) ℂ) * (rhMatrixAt k * rcMatrixAt k)))

end
end ResearchFormalizationBatch_01a0096e_5a75_7fe3_bebc_178cf02aa479
end MathlibPlus.Open
