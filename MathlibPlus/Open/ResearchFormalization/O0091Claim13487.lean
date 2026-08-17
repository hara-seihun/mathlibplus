import MathlibPlus.Open.Research.Batch13518_13519

open scoped BigOperators Matrix

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13487

abbrev Qubit := Fin 2
abbrev QIndex := Qubit × Qubit
abbrev LocalMatrix := Matrix Qubit Qubit ℂ
abbrev QMatrix := Matrix QIndex QIndex ℂ

def pauliI : LocalMatrix := 1

def pauliX : LocalMatrix := !![0, 1; 1, 0]

def tensor (A B : LocalMatrix) : QMatrix := Matrix.kronecker A B

def qZero (x : ℝ) : QMatrix :=
  (((2 + x) / 4 : ℝ) : ℂ) • tensor pauliI pauliI -
    ((1 / 2 : ℝ) : ℂ) • tensor pauliX pauliX

def xEigenvector (s : Qubit) : Qubit → ℂ :=
  if s = 0 then
    ![((1 / Real.sqrt 2 : ℝ) : ℂ), ((1 / Real.sqrt 2 : ℝ) : ℂ)]
  else
    ![((1 / Real.sqrt 2 : ℝ) : ℂ), (-(1 / Real.sqrt 2 : ℝ) : ℂ)]

def jointXProductBasis : QMatrix :=
  fun i j => xEigenvector j.1 i.1 * xEigenvector j.2 i.2

def jointXDiagonal (x : ℝ) : QMatrix :=
  fun i j =>
    if i = j then
      if i.1 = i.2 then (((x / 4 : ℝ) : ℂ))
      else (((4 + x) / 4 : ℝ) : ℂ)
    else 0

def projector (u : Qubit → ℂ) : LocalMatrix :=
  fun i j => u i * star (u j)

def explicitProductDecomposition (x : ℝ) : QMatrix :=
  (((x / 4 : ℝ) : ℂ) •
      (tensor (projector (xEigenvector 0)) (projector (xEigenvector 0)) +
        tensor (projector (xEigenvector 1)) (projector (xEigenvector 1)))) +
    (((4 + x) / 4 : ℝ) : ℂ) •
      (tensor (projector (xEigenvector 0)) (projector (xEigenvector 1)) +
        tensor (projector (xEigenvector 1)) (projector (xEigenvector 0)))

/-- At full Reynolds, the concrete Gram matrix has the two displayed weights
in the local joint-X product basis and the displayed local-projector
separable decomposition. -/
def claim13487 : Prop :=
  ∀ (x : ℝ), 0 ≤ x →
    Matrix.conjTranspose (jointXProductBasis) * qZero x * jointXProductBasis =
        jointXDiagonal x ∧
      qZero x = explicitProductDecomposition x ∧
      MathlibPlus.Open.Research.separableGram (qZero x) ∧
      MathlibPlus.Open.Research.splitLocalGram (qZero x)

end MathlibPlus.Open.ResearchFormalization.O0091Claim13487
