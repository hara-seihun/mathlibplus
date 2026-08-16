import Mathlib

noncomputable section

namespace MathlibPlus.Open

abbrev Two := Fin 2
abbrev TensorIndex := Two × Two
abbrev TwoMatrix := Matrix Two Two ℂ
abbrev TensorMatrix := Matrix TensorIndex TensorIndex ℂ
abbrev TensorVector := TensorIndex → ℂ

def pauliX : TwoMatrix := !![0, 1; 1, 0]

def pauliY : TwoMatrix := !![0, -Complex.I; Complex.I, 0]

def pauliZ : TwoMatrix := !![1, 0; 0, -1]

def phase (θ : ℝ) : ℂ := Complex.exp (Complex.I * ((θ : ℂ) / 2))

def pTheta (θ : ℝ) : TwoMatrix := !![phase θ, 0; 0, phase (-θ)]

def adjointTwo (A : TwoMatrix) : TwoMatrix :=
  fun i j => starRingEnd ℂ (A j i)

def cS (θ : ℝ) : TwoMatrix :=
  pTheta θ * pauliX * adjointTwo (pTheta θ)

def yTheta (θ : ℝ) : TwoMatrix :=
  pTheta θ * pauliY * adjointTwo (pTheta θ)

def tensorOp (A B : TwoMatrix) : TensorMatrix :=
  fun i j => A i.1 j.1 * B i.2 j.2

def rH (θ : ℝ) : TensorMatrix := tensorOp (cS θ) (1 : TwoMatrix)

def rC : TensorMatrix := tensorOp (1 : TwoMatrix) pauliX

def dOp (θ : ℝ) : TensorMatrix := rH θ * rC

def jOp : TensorMatrix := tensorOp pauliZ pauliY

def nOp (θ : ℝ) : TensorMatrix := tensorOp (yTheta θ) pauliZ

def spanCommutes (θ : ℝ) : Prop :=
  ∀ A B : TensorMatrix,
    A ∈ Submodule.span ℂ ({(1 : TensorMatrix), dOp θ, jOp, nOp θ} : Set TensorMatrix) →
    B ∈ Submodule.span ℂ ({(1 : TensorMatrix), dOp θ, jOp, nOp θ} : Set TensorMatrix) →
    A * B = B * A

def claim13661 : Prop :=
  ∀ θ : ℝ,
    (dOp θ) ^ 2 = (1 : TensorMatrix) ∧
    jOp ^ 2 = (1 : TensorMatrix) ∧
    (nOp θ) ^ 2 = (1 : TensorMatrix) ∧
    dOp θ * jOp = jOp * dOp θ ∧
    dOp θ * jOp = nOp θ ∧
    spanCommutes θ

def claim13662 : Prop :=
  ∀ θ : ℝ,
    (rH θ * dOp θ * rH θ = dOp θ ∧
      rH θ * jOp * rH θ = -jOp ∧
      rH θ * nOp θ * rH θ = -nOp θ) ∧
    (rC * dOp θ * rC = dOp θ ∧
      rC * jOp * rC = -jOp ∧
      rC * nOp θ * rC = -nOp θ)

def expReal (u : ℝ) : ℂ := Complex.exp (u : ℂ)

def hBase (U : ℝ) : Two → ℂ :=
  fun i => if i = 0 then expReal (U / 2) else expReal (-U / 2)

def cPhi (Φ : ℝ) : Two → ℂ :=
  fun i => if i = 0 then phase Φ else phase (-Φ)

def matVec (A : TwoMatrix) (v : Two → ℂ) : Two → ℂ :=
  fun i => ∑ j, A i j * v j

def hRay (U θ : ℝ) : Two → ℂ := matVec (pTheta θ) (hBase U)

def zTheta (θ U Φ : ℝ) : TensorVector :=
  fun i => hRay U θ i.1 * cPhi Φ i.2

def tensorMatVec (A : TensorMatrix) (v : TensorVector) : TensorVector :=
  fun i => ∑ j, A i j * v j

def hermitianInner (v w : TensorVector) : ℂ :=
  ∑ i, starRingEnd ℂ (v i) * w i

def qFamily (θ x g t : ℝ) : TensorMatrix :=
  (((2 + x : ℝ) : ℂ) / 4) • (1 : TensorMatrix) -
    ((1 : ℂ) / 2) • dOp θ -
    ((g : ℂ) / 4) • jOp +
    (t : ℂ) • nOp θ

def qExpectation (θ x g t U Φ : ℝ) : ℂ :=
  hermitianInner (zTheta θ U Φ)
    (tensorMatVec (qFamily θ x g t) (zTheta θ U Φ))

def claim13664 : Prop :=
  ∀ (θ x g t U Φ : ℝ),
    qExpectation θ x g t U Φ =
      (((2 + x) * Real.cosh U - 2 * Real.cos Φ +
        g * Real.sinh U * Real.sin Φ : ℝ) : ℂ)

end MathlibPlus.Open
