import Mathlib

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a00951

abbrev MatrixIndex2 := Fin 2 × Fin 2
abbrev Matrix2 := EuclideanSpace ℂ MatrixIndex2
abbrev Vec2 := Fin 2 → ℂ
abbrev TensorIndex2 := Fin 2 × Fin 2
abbrev TensorVec2 := TensorIndex2 → ℂ
abbrev TensorMatrix2 := EuclideanSpace ℂ (TensorIndex2 × TensorIndex2)

noncomputable section

noncomputable def matrixEntries (A : Matrix2) : MatrixIndex2 → ℂ :=
  EuclideanSpace.equiv MatrixIndex2 ℂ A

noncomputable def matrixOfEntries (a : MatrixIndex2 → ℂ) : Matrix2 :=
  (EuclideanSpace.equiv MatrixIndex2 ℂ).symm a

noncomputable def matrixOne2 : Matrix2 :=
  matrixOfEntries (fun q => if q.1 = q.2 then 1 else 0)

noncomputable def matrixMul2 (A B : Matrix2) : Matrix2 :=
  matrixOfEntries (fun q =>
    ∑ k : Fin 2, matrixEntries A (q.1, k) * matrixEntries B (k, q.2))

noncomputable def matrixStar2 (A : Matrix2) : Matrix2 :=
  matrixOfEntries (fun q => star (matrixEntries A (q.2, q.1)))

def matrixMulVec2 (A : Matrix2) (u : Vec2) : Vec2 :=
  fun i => ∑ j : Fin 2, matrixEntries A (i, j) * u j

noncomputable def hermitianQuadratic (A : Matrix2) (u : Vec2) : ℂ :=
  dotProduct (fun i => star (u i)) (matrixMulVec2 A u)

def matrixDet2 (A : Matrix2) : ℂ :=
  matrixEntries A (0, 0) * matrixEntries A (1, 1) -
    matrixEntries A (0, 1) * matrixEntries A (1, 0)

def matrixTrace2 (A : Matrix2) : ℂ :=
  ∑ i : Fin 2, matrixEntries A (i, i)

def matrixIsHermitian2 (A : Matrix2) : Prop :=
  ∀ i j : Fin 2, star (matrixEntries A (j, i)) = matrixEntries A (i, j)

def positiveSemidefinite2 (A : Matrix2) : Prop :=
  matrixIsHermitian2 A ∧ ∀ u : Vec2, 0 ≤ (hermitianQuadratic A u).re

def positiveDefinite2 (A : Matrix2) : Prop :=
  matrixIsHermitian2 A ∧ ∀ u : Vec2, u ≠ 0 → 0 < (hermitianQuadratic A u).re

def matrixPow2 (A : Matrix2) : ℕ → Matrix2
  | 0 => matrixOne2
  | n + 1 => matrixMul2 (matrixPow2 A n) A

noncomputable def matrixExp2 (A : Matrix2) : Matrix2 :=
  ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • matrixPow2 A n

def hostileP : ℝ := 1 / (1 + 5 * Real.sqrt 2)

def hostileG0 (a : ℝ) : ℝ :=
  hostileP * Real.exp (-(a / 4)) + (1 - hostileP) * Real.exp (-(a / 8))

noncomputable def hostileG0Matrix (A : Matrix2) : Matrix2 :=
  (hostileP : ℂ) • matrixExp2 ((-(1 / 4 : ℂ)) • A) +
    ((1 - hostileP : ℝ) : ℂ) • matrixExp2 ((-(1 / 8 : ℂ)) • A)

noncomputable def hostilePhi : Matrix2 → ℝ :=
  fun A => (matrixDet2 (hostileG0Matrix A)).re

def completelyMonotoneOnHermitianCone (Φ : Matrix2 → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ Φ {A : Matrix2 | positiveSemidefinite2 A} ∧
    ∀ (k : ℕ) (A : Matrix2) (C : Fin k → Matrix2),
      positiveDefinite2 A →
        (∀ j : Fin k, positiveSemidefinite2 (C j)) →
          0 ≤ ((-1 : ℝ) ^ k) * ((iteratedFDeriv ℝ k Φ A) C)

def unitary2 (U : Matrix2) : Prop :=
  matrixMul2 (matrixStar2 U) U = matrixOne2 ∧
    matrixMul2 U (matrixStar2 U) = matrixOne2

noncomputable def conjugate2 (U B : Matrix2) : Matrix2 :=
  matrixMul2 (matrixMul2 U B) (matrixStar2 U)

def diagonal0 (B : Matrix2) : ℝ := (matrixEntries B (0, 0)).re

def diagonal1 (B : Matrix2) : ℝ := (matrixEntries B (1, 1)).re

noncomputable def hostileTwoPointLaw : Measure ℝ :=
  ENNReal.ofReal hostileP • Measure.dirac (1 / 4 : ℝ) +
    ENNReal.ofReal (1 - hostileP) • Measure.dirac (1 / 8 : ℝ)

def hostileTwoPointNondegenerate : Prop :=
  0 < hostileP ∧ hostileP < 1 ∧ (1 / 4 : ℝ) ≠ 1 / 8

def invariantPSD2ConeLaw (μ : Measure Matrix2) : Prop :=
  IsProbabilityMeasure μ ∧
    μ {B : Matrix2 | positiveSemidefinite2 B} = 1 ∧
      ∀ U : Matrix2, unitary2 U → Measure.map (conjugate2 U) μ = μ

def hostileConeLaplaceRepresentation (μ : Measure Matrix2) : Prop :=
  ∀ A : Matrix2, positiveSemidefinite2 A →
    hostilePhi A =
      ∫ B, Real.exp (-((matrixTrace2 (matrixMul2 A B)).re)) ∂μ

def claim13613 : Prop :=
  completelyMonotoneOnHermitianCone hostilePhi →
    ∃ μ : Measure Matrix2,
      invariantPSD2ConeLaw μ ∧
        hostileConeLaplaceRepresentation μ ∧
          hostileTwoPointNondegenerate ∧
            ProbabilityTheory.IndepFun diagonal0 diagonal1 μ ∧
            Measure.map diagonal0 μ = hostileTwoPointLaw ∧
              Measure.map diagonal1 μ = hostileTwoPointLaw

def hostileScalarSource (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2)) + 10 * Real.exp (-(2 * t ^ 2))

def claim13615 : Prop :=
  (∀ t : ℝ, 0 < hostileScalarSource t) ∧
    ¬ completelyMonotoneOnHermitianCone hostilePhi

def unitSphere2 (u : Vec2) : Prop :=
  ∑ i : Fin 2, Complex.normSq (u i) = 1

def rayleighQuotient2 (B : Matrix2) (u : Vec2) : ℝ :=
  (hermitianQuadratic B u).re

def claim13614 : Prop :=
  ∀ B : Matrix2, matrixIsHermitian2 B →
    (∀ u : Vec2, unitSphere2 u →
      rayleighQuotient2 B u ∈ ({(1 / 8 : ℝ), (1 / 4 : ℝ)} : Set ℝ)) →
        ∃ c : ℝ, B = (c : ℂ) • matrixOne2

noncomputable def xMatrix : Matrix2 :=
  matrixOfEntries (fun q =>
    if (q.1 = 0 ∧ q.2 = 1) ∨ (q.1 = 1 ∧ q.2 = 0) then 1 else 0)

noncomputable def matrixDiagonal2 (d : Fin 2 → ℂ) : Matrix2 :=
  matrixOfEntries (fun q => if q.1 = q.2 then d q.1 else 0)

noncomputable def pTheta (θ : ℝ) : Matrix2 :=
  matrixDiagonal2 (fun i =>
    if i = 0 then
      Complex.exp (Complex.I * (θ : ℂ) / 2)
    else
      Complex.exp (-(Complex.I * (θ : ℂ) / 2)))

def cVector (Φ : ℝ) : Vec2 :=
  fun i =>
    if i = 0 then
      Complex.exp (Complex.I * (Φ : ℂ) / 2)
    else
      Complex.exp (-(Complex.I * (Φ : ℂ) / 2))

def hBaseVector (U : ℝ) : Vec2 :=
  fun i => if i = 0 then Complex.exp ((U : ℂ) / 2) else Complex.exp (-(U : ℂ) / 2)

noncomputable def hVector (U θ : ℝ) : Vec2 :=
  matrixMulVec2 (pTheta θ) (hBaseVector U)

noncomputable def cMatrix (θ : ℝ) : Matrix2 :=
  matrixMul2 (matrixMul2 (pTheta θ) xMatrix) (matrixStar2 (pTheta θ))

def tensorVector (u c : Vec2) : TensorVec2 :=
  fun q => u q.1 * c q.2

def rowVectorization (M : Matrix2) : TensorVec2 :=
  fun q => matrixEntries M q

noncomputable def tensorEntries (A : TensorMatrix2) : TensorIndex2 × TensorIndex2 → ℂ :=
  EuclideanSpace.equiv (TensorIndex2 × TensorIndex2) ℂ A

noncomputable def tensorOfEntries (a : TensorIndex2 × TensorIndex2 → ℂ) : TensorMatrix2 :=
  (EuclideanSpace.equiv (TensorIndex2 × TensorIndex2) ℂ).symm a

noncomputable def tensorKronecker (A B : Matrix2) : TensorMatrix2 :=
  tensorOfEntries (fun q =>
    matrixEntries A (q.1.1, q.2.1) * matrixEntries B (q.1.2, q.2.2))

noncomputable def tensorMul (A B : TensorMatrix2) : TensorMatrix2 :=
  tensorOfEntries (fun q =>
    ∑ k : TensorIndex2, tensorEntries A (q.1, k) * tensorEntries B (k, q.2))

def tensorMulVec (A : TensorMatrix2) (v : TensorVec2) : TensorVec2 :=
  fun i => ∑ j : TensorIndex2, tensorEntries A (i, j) * v j

noncomputable def rayActionH (θ : ℝ) : TensorMatrix2 :=
  tensorKronecker (cMatrix θ) matrixOne2

noncomputable def rayActionC : TensorMatrix2 :=
  tensorKronecker matrixOne2 xMatrix

def pairedCorner (θ : ℝ) : Set Matrix2 :=
  {M |
    tensorMulVec (tensorMul (rayActionH θ) rayActionC) (rowVectorization M) =
      rowVectorization M}

noncomputable def gaugedPairedCorner (θ : ℝ) : Set Matrix2 :=
  {M | ∃ a b : ℂ,
    M = matrixMul2 (pTheta θ) (a • matrixOne2 + b • xMatrix)}

def claim13660 : Prop :=
  ∀ U θ Φ : ℝ,
    matrixMulVec2 (cMatrix θ) (hVector U θ) = hVector (-U) θ ∧
      matrixMulVec2 xMatrix (cVector Φ) = cVector (-Φ) ∧
        tensorMulVec (rayActionH θ) (tensorVector (hVector U θ) (cVector Φ)) =
          tensorVector (hVector (-U) θ) (cVector Φ) ∧
          tensorMulVec rayActionC (tensorVector (hVector U θ) (cVector Φ)) =
            tensorVector (hVector U θ) (cVector (-Φ)) ∧
            tensorMul (rayActionH θ) rayActionC = tensorMul rayActionC (rayActionH θ) ∧
              pairedCorner θ = gaugedPairedCorner θ

end

end MathlibPlus.Open.ResearchFormalizationBatch_01a00951
