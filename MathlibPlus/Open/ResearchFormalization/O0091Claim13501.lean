import MathlibPlus.Open.ResearchFormalization.O0091Claim13487
import MathlibPlus.Open.LinearAlgebra.BatchO0091
import MathlibPlus.Open.Research.Batch13518_13519

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13501

noncomputable section

open MathlibPlus.Open.Research
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Qubit := Fin 2
abbrev QMatrix := Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ
abbrev LocalMatrix := Matrix Qubit Qubit ℂ

noncomputable def xPlusVector : Qubit → ℂ :=
  ![((1 / Real.sqrt 2 : ℝ) : ℂ), ((1 / Real.sqrt 2 : ℝ) : ℂ)]

noncomputable def xMinusVector : Qubit → ℂ :=
  ![((1 / Real.sqrt 2 : ℝ) : ℂ), (-(1 / Real.sqrt 2 : ℝ) : ℂ)]

noncomputable def zPlusVector : Qubit → ℂ := ![1, 0]
noncomputable def zMinusVector : Qubit → ℂ := ![0, 1]

noncomputable def yPlusVector : Qubit → ℂ :=
  ![((1 / Real.sqrt 2 : ℝ) : ℂ), (Complex.I / Real.sqrt 2)]

noncomputable def yMinusVector : Qubit → ℂ :=
  ![((1 / Real.sqrt 2 : ℝ) : ℂ), (-Complex.I / Real.sqrt 2)]

noncomputable def xProjector (positive : Bool) : LocalMatrix :=
  projector (if positive then xPlusVector else xMinusVector)

noncomputable def zProjector (positive : Bool) : LocalMatrix :=
  projector (if positive then zPlusVector else zMinusVector)

noncomputable def yProjector (positive : Bool) : LocalMatrix :=
  projector (if positive then yPlusVector else yMinusVector)

noncomputable def identityProductProjectors : QMatrix :=
  ∑ e : Qubit, ∑ f : Qubit,
    tensor (xProjector (e = 0)) (xProjector (f = 0))

noncomputable def oppositeXProductProjectors : QMatrix :=
  tensor (xProjector true) (xProjector false) +
    tensor (xProjector false) (xProjector true)

noncomputable def signedZYProductProjectors (g : ℝ) : QMatrix :=
  if Real.sign g = 1 then
    tensor (zProjector true) (yProjector false) +
      tensor (zProjector false) (yProjector true)
  else
    tensor (zProjector true) (yProjector true) +
      tensor (zProjector false) (yProjector false)

noncomputable def explicitSeparableRepresentative (x g : ℝ) : QMatrix :=
  (((x - |g|) / 4 : ℝ) : ℂ) • identityProductProjectors +
    oppositeXProductProjectors +
    (((|g| / 2 : ℝ) : ℂ) • signedZYProductProjectors g)

/-- The visible zero-gauge matrix and all three completion predicates retain
 the reviewed two-qubit Pauli carrier. -/
def explicitSeparableRepresentative_claim13501 : Prop :=
  ∀ x g : ℝ, 0 ≤ x → x ≤ 1 →
    (visibleGram x g =
      (((x - |g|) / 4 : ℝ) : ℂ) • tensor pauliI pauliI +
        (((2 : ℝ) / 4 : ℝ) : ℂ) •
          (tensor pauliI pauliI - tensor pauliX pauliX) +
        (((|g| / 4 : ℝ) : ℝ) : ℂ) •
          (tensor pauliI pauliI -
            ((Real.sign g : ℂ) • tensor pauliZ pauliY))) ∧
    (projector xPlusVector =
        ((1 / 2 : ℝ) : ℂ) • (pauliI + pauliX) ∧
      projector xMinusVector =
        ((1 / 2 : ℝ) : ℂ) • (pauliI - pauliX) ∧
      projector zPlusVector =
        ((1 / 2 : ℝ) : ℂ) • (pauliI + pauliZ) ∧
      projector zMinusVector =
        ((1 / 2 : ℝ) : ℂ) • (pauliI - pauliZ) ∧
      projector yPlusVector =
        ((1 / 2 : ℝ) : ℂ) • (pauliI + pauliY) ∧
      projector yMinusVector =
        ((1 / 2 : ℝ) : ℂ) • (pauliI - pauliY)) ∧
    (|g| ≤ x →
      visibleGram x g = explicitSeparableRepresentative x g ∧
      0 ≤ (x - |g|) / 4 ∧
      0 ≤ (|g| / 2 : ℝ) ∧
      separableGram (visibleGram x g)) ∧
    (pptCompletion x g ↔ |g| ≤ x) ∧
    (separableCompletion x g ↔ |g| ≤ x)

end

end MathlibPlus.Open.ResearchFormalization.O0091Claim13501
