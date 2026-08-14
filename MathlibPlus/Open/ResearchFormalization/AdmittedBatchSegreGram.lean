import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.SegreGram

abbrev SegreIndex := Fin 2 × Fin 2
abbrev SegreMatrix := Matrix SegreIndex SegreIndex ℂ

noncomputable def segreVector (U Φ : ℝ) : SegreIndex → ℂ := fun p =>
  if p.1 = 0 then
    if p.2 = 0 then
      Complex.exp (((U : ℂ) + (Φ : ℂ) * Complex.I) / 2)
    else
      Complex.exp (((U : ℂ) - (Φ : ℂ) * Complex.I) / 2)
  else if p.2 = 0 then
    Complex.exp (((-U : ℂ) + (Φ : ℂ) * Complex.I) / 2)
  else
    Complex.exp (((-U : ℂ) - (Φ : ℂ) * Complex.I) / 2)

def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

def pauliTensor (A B : Matrix (Fin 2) (Fin 2) ℂ) : SegreMatrix :=
  Matrix.kronecker A B

def pauliExpectation (A : SegreMatrix) (z : SegreIndex → ℂ) : ℂ :=
  ∑ p, star (z p) * (Matrix.mulVec A z) p

noncomputable def segreGram (x g t : ℝ) : SegreMatrix :=
  ((2 + x : ℂ) / 4) • (1 : SegreMatrix) -
      (1 / 2 : ℂ) • pauliTensor pauliX pauliX -
      ((g : ℂ) / 4) • pauliTensor pauliZ pauliY +
      (t : ℂ) • pauliTensor pauliY pauliZ

def exactSegreGramFamily : Prop :=
  (∀ U Φ : ℝ,
      pauliExpectation (1 : SegreMatrix) (segreVector U Φ) =
          (4 * Real.cosh U : ℂ) ∧
        pauliExpectation (pauliTensor pauliX pauliX) (segreVector U Φ) =
          (4 * Real.cos Φ : ℂ) ∧
        pauliExpectation (pauliTensor pauliZ pauliY) (segreVector U Φ) =
          (-4 * Real.sinh U * Real.sin Φ : ℂ) ∧
        pauliExpectation (pauliTensor pauliY pauliZ) (segreVector U Φ) = 0) ∧
    (∀ (U Φ x g t : ℝ),
      pauliExpectation (segreGram x g t) (segreVector U Φ) =
        ((2 + x) * Real.cosh U - 2 * Real.cos Φ +
            g * Real.sinh U * Real.sin Φ : ℝ))

end MathlibPlus.Open.ResearchFormalization.SegreGram
