import MathlibPlus.Open.LinearAlgebra.BatchO0091
import MathlibPlus.Open.Research.BellCanonicalBatch

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0091RowVectorizationBellFrame13503

noncomputable section

abbrev QMatrix := MathlibPlus.Open.LinearAlgebra.QMatrix
abbrev TwoQubit := MathlibPlus.Open.LinearAlgebra.TwoQubit

/-- Row-vectorization in the ordered pair carrier `(Fin 2) × (Fin 2)`. -/
def rvec (M : QMatrix) : TwoQubit → ℂ :=
  MathlibPlus.Open.LinearAlgebra.rowVec M

/-- The tensor product of two column vectors in the row-vectorized carrier. -/
def tensorVector (u c : Fin 2 → ℂ) : TwoQubit → ℂ :=
  fun ij => u ij.1 * c ij.2

/-- The rank-one endomorphism attached to two column vectors. -/
def outerProduct (u c : Fin 2 → ℂ) : QMatrix :=
  fun i j => u i * c j

/-- Right multiplication by the transpose in the endomorphism carrier. -/
def leftRightProduct (A B M : QMatrix) : QMatrix :=
  MathlibPlus.Open.LinearAlgebra.qmul
    (MathlibPlus.Open.LinearAlgebra.qmul A M)
    (fun i j => B j i)

/-- The Bell columns of the reviewed computational Bell matrix. -/
def bellFrameVector (k : Fin 4) : TwoQubit → ℂ :=
  fun ij =>
    MathlibPlus.Open.Research.bellFrame
      (finProdFinEquiv ij) k

/-- The same four columns written in the Pauli endomorphism frame. -/
def bellPauliFrame : Fin 4 → TwoQubit → ℂ :=
  ![
    ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      rvec MathlibPlus.Open.LinearAlgebra.pauliI,
    ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      rvec MathlibPlus.Open.LinearAlgebra.pauliX,
    ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      rvec MathlibPlus.Open.LinearAlgebra.pauliZ,
    ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      rvec (Complex.I • MathlibPlus.Open.LinearAlgebra.pauliY)
  ]

/-- The full four-dimensional span carried by the Bell frame. -/
def bellFrameSpans : Prop :=
  ∀ v : TwoQubit → ℂ,
    ∃ coeff : Fin 4 → ℂ,
      v = ∑ i : Fin 4, coeff i • bellFrameVector i

/-- Uniqueness of coordinates in the Bell frame. -/
def bellFrameIndependent : Prop :=
  ∀ coeff : Fin 4 → ℂ,
    (∑ i : Fin 4, coeff i • bellFrameVector i) = 0 →
      ∀ i : Fin 4, coeff i = 0

/-- The traceless endomorphism carrier `sl₂`. -/
def tracelessMatrix (M : QMatrix) : Prop :=
  Matrix.trace M = 0

/-- The scalar line and the traceless Pauli carrier form a direct sum. -/
def scalarTracelessDecomposition : Prop :=
  (∀ M : QMatrix,
    ∃ a : ℂ, ∃ T : QMatrix,
      tracelessMatrix T ∧
        M = a • MathlibPlus.Open.LinearAlgebra.pauliI + T) ∧
  (∀ a : ℂ, ∀ T : QMatrix,
    tracelessMatrix T →
      a • MathlibPlus.Open.LinearAlgebra.pauliI + T = 0 →
        a = 0 ∧ T = 0)

/-- Claim 13503: row-vectorization identifies tensor products with left/right
endomorphism multiplication, rank-one tensors with outer products, and the
reviewed Bell frame with the full scalar-plus-traceless decomposition. -/
def claim13503 : Prop :=
  (∀ A B M : QMatrix,
    MathlibPlus.Open.LinearAlgebra.tensorAction A B (rvec M) =
      rvec (leftRightProduct A B M)) ∧
  (∀ u c : Fin 2 → ℂ,
    tensorVector u c = rvec (outerProduct u c)) ∧
  (bellFrameVector = bellPauliFrame) ∧
  bellFrameSpans ∧
  bellFrameIndependent ∧
  scalarTracelessDecomposition

end

end MathlibPlus.Open.ResearchFormalization.O0091RowVectorizationBellFrame13503
