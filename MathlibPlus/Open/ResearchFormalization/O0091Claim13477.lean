import Mathlib

open scoped BigOperators Matrix

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13477

abbrev Qubit := Fin 2
abbrev QIndex := Qubit × Qubit
abbrev LocalMatrix := Matrix Qubit Qubit ℂ
abbrev QMatrix := Matrix QIndex QIndex ℂ

def pauliI : LocalMatrix := 1

def pauliX : LocalMatrix := !![0, 1; 1, 0]

def pauliY : LocalMatrix := !![0, -Complex.I; Complex.I, 0]

def pauliZ : LocalMatrix := !![1, 0; 0, -1]

def tensor (A B : LocalMatrix) : QMatrix := Matrix.kronecker A B

def qFamily (x g t : ℝ) : QMatrix :=
  (((2 + x) / 4 : ℝ) : ℂ) • tensor pauliI pauliI
    - ((1 / 2 : ℝ) : ℂ) • tensor pauliX pauliX
    - ((g / 4 : ℝ) : ℂ) • tensor pauliZ pauliY
    + (t : ℂ) • tensor pauliY pauliZ

def S : QMatrix := tensor pauliX pauliI

def T : QMatrix := tensor pauliI pauliX

def heat (lam : ℝ) (A : QMatrix) : QMatrix :=
  (((1 + lam) / 4 : ℝ) : ℂ) •
      (A + (S * T) * A * (S * T))
    + (((1 - lam) / 4 : ℝ) : ℂ) •
      (S * A * S + T * A * T)

def segreVector (U Φ : ℝ) : QIndex → ℂ := fun p =>
  if p.1 = 0 then
    if p.2 = 0 then
      Complex.exp (((U : ℂ) + (Φ : ℂ) * Complex.I) / 2)
    else
      Complex.exp (((U : ℂ) - (Φ : ℂ) * Complex.I) / 2)
  else if p.2 = 0 then
    Complex.exp (((-U : ℂ) + (Φ : ℂ) * Complex.I) / 2)
  else
    Complex.exp (((-U : ℂ) - (Φ : ℂ) * Complex.I) / 2)

def segreExpectation (A : QMatrix) (z : QIndex → ℂ) : ℂ :=
  ∑ p, star (z p) * (A.mulVec z) p

/-- The concrete heat covariance and transformed Segre evaluation of the
admitted two-qubit Gram family. -/
def claim13477 : Prop :=
  ∀ (x g t lam U Φ : ℝ),
    heat lam (qFamily x g t) = qFamily x (lam * g) (lam * t) ∧
      segreExpectation (heat lam (qFamily x g t)) (segreVector U Φ) =
        (((2 + x) * Real.cosh U - 2 * Real.cos Φ +
          lam * g * Real.sinh U * Real.sin Φ : ℝ) : ℂ)

end MathlibPlus.Open.ResearchFormalization.O0091Claim13477
