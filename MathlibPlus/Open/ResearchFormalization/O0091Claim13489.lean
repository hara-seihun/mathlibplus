import MathlibPlus.Open.ResearchFormalization.O0091Claim13480
import MathlibPlus.Open.LinearAlgebra.BatchO0091

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13489

noncomputable section

open scoped Matrix

abbrev Qubit := MathlibPlus.Open.ResearchFormalization.O0091Claim13480.Qubit
abbrev QIndex := MathlibPlus.Open.ResearchFormalization.O0091Claim13480.QIndex
abbrev QMatrix := MathlibPlus.Open.ResearchFormalization.O0091Claim13480.QMatrix
abbrev JointIndex := MathlibPlus.Open.LinearAlgebra.JointIndex
abbrev JointMatrix := MathlibPlus.Open.LinearAlgebra.JointMatrix

/-- The permutation from the original joint-X order
    (++,+-,-+,--) to (++ ,-- ,+- ,-+). -/
def reorderIndex (i : JointIndex) : JointIndex :=
  if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1 else 2

/-- Reindex a matrix into the required parity-first joint-X order. -/
def reorderedSchurMatrix (lam : ℝ) : JointMatrix :=
  fun i j =>
    MathlibPlus.Open.LinearAlgebra.heatSchurMatrix lam
      (reorderIndex i) (reorderIndex j)

def relativeBlockMatrix (lam : ℝ) : Matrix Qubit Qubit ℂ :=
  !![1, (lam : ℂ); (lam : ℂ), 1]

def reorderedQIndex (i : JointIndex) : QIndex :=
  if i = 0 then (0, 0)
  else if i = 1 then (0, 1)
  else if i = 2 then (1, 0)
  else (1, 1)

def qMatrixToJoint (A : QMatrix) : JointMatrix :=
  fun i j => A (reorderedQIndex i) (reorderedQIndex j)

def parityRelativeMatrix (lam : ℝ) : JointMatrix :=
  qMatrixToJoint
    (MathlibPlus.Open.ResearchFormalization.O0091Claim13480.tensor
      MathlibPlus.Open.ResearchFormalization.O0091Claim13480.pauliI
      (relativeBlockMatrix lam))

def reorderedSchurChannel (lam : ℝ) (A : JointMatrix) : JointMatrix :=
  MathlibPlus.Open.LinearAlgebra.schurMultiply
    (reorderedSchurMatrix lam) A

def jointBasisDephasing (A : JointMatrix) : JointMatrix :=
  fun i j => if i = j then A i j else 0

def sameParityFlag (i j : JointIndex) : Prop :=
  (reorderedQIndex i).1 = (reorderedQIndex j).1

def factorChannelOnReorderedBasis (lam : ℝ) : Prop :=
  ∀ A : QMatrix,
    MathlibPlus.Open.ResearchFormalization.O0091Claim13480.heatInReorderedJointX
        lam A =
      MathlibPlus.Open.ResearchFormalization.O0091Claim13480.idParityTensorDephasing
        lam A

/-- Claim 13489: explicit parity-first reordering gives the two identical
    relative-qubit Schur blocks, and the concrete heat channel factors through
    the reviewed parity-flag/relative-qubit dephasing carrier. -/
def claim13489 : Prop :=
  (∀ lam : ℝ,
    reorderedSchurMatrix lam = parityRelativeMatrix lam) ∧
    (∀ lam : ℝ, factorChannelOnReorderedBasis lam) ∧
    (∀ A : JointMatrix, ∀ i j : JointIndex,
      sameParityFlag i j →
        reorderedSchurChannel 1 A i j = A i j) ∧
    (∀ A : JointMatrix,
      reorderedSchurChannel 0 A = jointBasisDephasing A)

end

end MathlibPlus.Open.ResearchFormalization.O0091Claim13489
