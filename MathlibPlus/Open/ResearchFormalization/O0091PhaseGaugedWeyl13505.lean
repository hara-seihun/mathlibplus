import MathlibPlus.Open.ResearchFormalization.O0091Claim13477
import MathlibPlus.Open.LinearAlgebra.BatchO0091

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0091PhaseGaugedWeyl13505

noncomputable section

abbrev Qubit := MathlibPlus.Open.ResearchFormalization.O0091Claim13477.Qubit
abbrev QIndex := MathlibPlus.Open.ResearchFormalization.O0091Claim13477.QIndex
abbrev LocalMatrix := MathlibPlus.Open.ResearchFormalization.O0091Claim13477.LocalMatrix
abbrev QMatrix := MathlibPlus.Open.ResearchFormalization.O0091Claim13477.QMatrix

/-- The phase gauge `P_θ` with `θ=t log 2`. -/
def phaseGauge (t : ℝ) : LocalMatrix :=
  !![
    Complex.exp (Complex.I * ((t * Real.log 2 : ℝ) : ℂ) / 2), 0;
    0, Complex.exp (-Complex.I * ((t * Real.log 2 : ℝ) : ℂ) / 2)]

/-- The phase-gauged first-coordinate Weyl involution. -/
def phaseConjugateX (t : ℝ) : LocalMatrix :=
  phaseGauge t * MathlibPlus.Open.ResearchFormalization.O0091Claim13477.pauliX *
    Matrix.conjTranspose (phaseGauge t)

/-- The two commuting two-qubit involutions. -/
def relativeWeylH (t : ℝ) : QMatrix :=
  MathlibPlus.Open.ResearchFormalization.O0091Claim13477.tensor
    (phaseConjugateX t)
    MathlibPlus.Open.ResearchFormalization.O0091Claim13477.pauliI

def relativeWeylC : QMatrix :=
  MathlibPlus.Open.ResearchFormalization.O0091Claim13477.tensor
    MathlibPlus.Open.ResearchFormalization.O0091Claim13477.pauliI
    MathlibPlus.Open.ResearchFormalization.O0091Claim13477.pauliX

/-- Matrix self-adjointness in the concrete complex matrix carrier. -/
def selfAdjoint (M : LocalMatrix) : Prop :=
  ∀ i j, M i j = star (M j i)

def selfAdjointQ (M : QMatrix) : Prop :=
  ∀ i j, M i j = star (M j i)

/-- The un-gauged hyperbolic and circular factor vectors. -/
def hyperbolicVector (U : ℝ) : Qubit → ℂ :=
  ![Complex.exp ((U : ℂ) / 2), Complex.exp (-((U : ℂ) / 2))]

def circularVector (Φ : ℝ) : Qubit → ℂ :=
  ![Complex.exp (Complex.I * (Φ : ℂ) / 2),
    Complex.exp (-Complex.I * (Φ : ℂ) / 2)]

/-- The exact phase-gauged Segre ray. -/
def phaseGaugedSegre (t U Φ : ℝ) : QIndex → ℂ :=
  fun p =>
    (phaseGauge t).mulVec (hyperbolicVector U) p.1 *
      circularVector Φ p.2

/-- The paired-corner eigenspace of simultaneous conjugation by `C_s`. -/
def pairedCorner (t : ℝ) : Set LocalMatrix :=
  {M | phaseConjugateX t * M * phaseConjugateX t = M}

/-- The unitary transport of the scalar-plus-Weyl corner. -/
def transportedCorner (t : ℝ) : Set LocalMatrix :=
  Set.image
    (fun M : LocalMatrix =>
      phaseGauge t * M * Matrix.conjTranspose (phaseGauge t))
    (↑(Submodule.span ℂ
      ({MathlibPlus.Open.ResearchFormalization.O0091Claim13477.pauliI,
        MathlibPlus.Open.ResearchFormalization.O0091Claim13477.pauliX} :
        Set LocalMatrix)) : Set LocalMatrix)

/-- Claim 13505: the phase-gauged Weyl operators are commuting self-adjoint
involutions, act on the transported Segre ray by the two sign reversals, and
transport the exact paired corner. -/
def claim13505 : Prop :=
  ∀ t : ℝ,
    let P := phaseGauge t
    let C := phaseConjugateX t
    let Rh := relativeWeylH t
    let Rc := relativeWeylC
    (P * Matrix.conjTranspose P = 1 ∧
      Matrix.conjTranspose P * P = 1) ∧
      selfAdjoint C ∧
        C * C = 1 ∧
          selfAdjointQ Rh ∧
            Rh * Rh = 1 ∧
              selfAdjointQ Rc ∧
                Rc * Rc = 1 ∧
                  Rh * Rc = Rc * Rh ∧
                    (∀ U Φ : ℝ,
                      Rh.mulVec (phaseGaugedSegre t U Φ) =
                          phaseGaugedSegre t (-U) Φ ∧
                        Rc.mulVec (phaseGaugedSegre t U Φ) =
                          phaseGaugedSegre t U (-Φ)) ∧
                      pairedCorner t = transportedCorner t

end

end MathlibPlus.Open.ResearchFormalization.O0091PhaseGaugedWeyl13505
