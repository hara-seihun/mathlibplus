import Mathlib

open scoped BigOperators Matrix

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13480

abbrev Qubit := Fin 2
abbrev QIndex := Qubit × Qubit
abbrev LocalMatrix := Matrix Qubit Qubit ℂ
abbrev QMatrix := Matrix QIndex QIndex ℂ

def pauliI : LocalMatrix := 1

def pauliX : LocalMatrix := !![0, 1; 1, 0]

def pauliY : LocalMatrix := !![0, -Complex.I; Complex.I, 0]

def pauliZ : LocalMatrix := !![1, 0; 0, -1]

def tensor (A B : LocalMatrix) : QMatrix := Matrix.kronecker A B

def S : QMatrix := tensor pauliX pauliI

def T : QMatrix := tensor pauliI pauliX

def heat (lam : ℝ) (A : QMatrix) : QMatrix :=
  (((1 + lam) / 4 : ℝ) : ℂ) •
      (A + (S * T) * A * (S * T))
    + (((1 - lam) / 4 : ℝ) : ℂ) •
      (S * A * S + T * A * T)

def xEigenvector (s : Qubit) : Qubit → ℂ :=
  if s = 0 then
    ![((1 / Real.sqrt 2 : ℝ) : ℂ), ((1 / Real.sqrt 2 : ℝ) : ℂ)]
  else
    ![((1 / Real.sqrt 2 : ℝ) : ℂ), (-(1 / Real.sqrt 2 : ℝ) : ℂ)]

def oldJointXIndex (p : QIndex) : QIndex :=
  if p.1 = 0 then
    if p.2 = 0 then (0, 0) else (1, 1)
  else if p.2 = 0 then (0, 1) else (1, 0)

def reorderedJointXBasis : QMatrix :=
  fun i j =>
    xEigenvector (oldJointXIndex j).1 i.1 *
      xEigenvector (oldJointXIndex j).2 i.2

def heatInReorderedJointX (lam : ℝ) (A : QMatrix) : QMatrix :=
  Matrix.conjTranspose reorderedJointXBasis *
      heat lam (reorderedJointXBasis * A *
        Matrix.conjTranspose reorderedJointXBasis) *
    reorderedJointXBasis

def localXSign (i : Qubit) : ℂ := if i = 0 then 1 else -1

def heatCoefficient (lam : ℝ) (i j : QIndex) : ℂ :=
  (((1 + lam) / 4 : ℝ) : ℂ) *
      (1 + localXSign i.1 * localXSign i.2 *
        localXSign j.1 * localXSign j.2) +
    (((1 - lam) / 4 : ℝ) : ℂ) *
      (localXSign i.1 * localXSign j.1 +
        localXSign i.2 * localXSign j.2)

def coefficientHeat (lam : ℝ) (A : QMatrix) : QMatrix :=
  fun i j => heatCoefficient lam (oldJointXIndex i) (oldJointXIndex j) * A i j

def relativeDephasing (lam : ℝ) (A : LocalMatrix) : LocalMatrix :=
  (((1 + lam) / 2 : ℝ) : ℂ) • A +
    (((1 - lam) / 2 : ℝ) : ℂ) • (pauliX * A * pauliX)

def simultaneousOrientationEven (A : QMatrix) : Prop :=
  ∀ i j, i.1 ≠ j.1 → A i j = 0

def idParityTensorDephasing (lam : ℝ) (A : QMatrix) : QMatrix :=
  fun i j =>
    if i.1 = j.1 then
      (relativeDephasing lam
        (fun a b => A (i.1, a) (i.1, b))) i.2 j.2
    else 0

def pauliMultiplierStatement (lam : ℝ) : Prop :=
  relativeDephasing lam pauliI = pauliI ∧
    relativeDephasing lam pauliX = pauliX ∧
    relativeDephasing lam pauliY = (lam : ℂ) • pauliY ∧
    relativeDephasing lam pauliZ = (lam : ℂ) • pauliZ

def canonicalDiagonal (x : ℝ) : LocalMatrix :=
  !![(((x / 4 : ℝ) : ℂ)), 0; 0, (((4 + x) / 4 : ℝ) : ℂ)]

def canonicalFactor (x ρ : ℝ) : QMatrix :=
  tensor (canonicalDiagonal x)
    (pauliI - (ρ : ℂ) • pauliY)

/-- On the concrete reordered joint-X carrier, heat is identity on the parity
flag tensored with qubit dephasing, including the Pauli multipliers and the
canonical factorization parameter action. -/
def claim13480 : Prop :=
  ∀ (lam : ℝ),
    (∀ A : QMatrix,
      heatInReorderedJointX lam A = coefficientHeat lam A) ∧
    (∀ A : QMatrix,
      simultaneousOrientationEven A →
        heatInReorderedJointX lam A = idParityTensorDephasing lam A) ∧
    pauliMultiplierStatement lam ∧
    (∀ (x ρ : ℝ),
      heatInReorderedJointX lam (canonicalFactor x ρ) =
        canonicalFactor x (lam * ρ))

end MathlibPlus.Open.ResearchFormalization.O0091Claim13480
