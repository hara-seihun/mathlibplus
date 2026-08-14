import Mathlib

namespace MathlibPlus.Open.ResearchBatch.DiagonalKernels

open scoped BigOperators

noncomputable section

abbrev P3 := MvPolynomial (Fin 3) ℚ
abbrev P2 := MvPolynomial (Fin 2) ℚ

/-- The three variables in `ℚ[X,Y,Z]`. -/
def X : P3 := MvPolynomial.X 0
def Y : P3 := MvPolynomial.X 1
def Z : P3 := MvPolynomial.X 2

/-- The two variables in the target `ℚ[p,q]`. -/
def pVar : P2 := MvPolynomial.X 0
def qVar : P2 := MvPolynomial.X 1

def diagonalPPQ (f : P3) : P2 :=
  MvPolynomial.eval₂Hom (algebraMap ℚ P2) (fun i =>
    if i = 0 then pVar else if i = 1 then pVar else qVar) f

def diagonalPQQ (f : P3) : P2 :=
  MvPolynomial.eval₂Hom (algebraMap ℚ P2) (fun i =>
    if i = 0 then pVar else if i = 1 then qVar else qVar) f

/-- The first diagonal map. -/
def firstDiagonalMap (f : P3) : P2 :=
  pVar * diagonalPPQ f + qVar * diagonalPQQ f

/-- The second diagonal map. -/
def secondDiagonalMap (f : P3) : P2 :=
  -pVar * diagonalPPQ f + qVar * diagonalPQQ f

/-- The displayed generators. -/
def g₁ : P3 := (X - Y) * (Y - Z)
def g₃ : P3 := X ^ 2 - X * Z - Y ^ 2 + Z ^ 2
def ell : P3 := X - Y + Z

/-- The embedded `ℚ[X,Z]` summand: no monomial contains a positive power of
`Y`. -/
def IsXZPolynomial (v : P3) : Prop :=
  ∀ d : Fin 3 →₀ ℕ, d 1 ≠ 0 → MvPolynomial.coeff d v = 0

/-- Direct-sum decomposition of the first diagonal kernel. -/
def firstDiagonalKernelDecomposition : Prop :=
  ∀ f : P3,
    firstDiagonalMap f = 0 ↔
      ∃! uv : P3 × P3,
        IsXZPolynomial uv.2 ∧ f = g₁ * uv.1 + g₃ * uv.2

/-- Direct-sum decomposition of the second diagonal kernel. -/
def secondDiagonalKernelDecomposition : Prop :=
  ∀ f : P3,
    secondDiagonalMap f = 0 ↔
      ∃! uv : P3 × P3,
        IsXZPolynomial uv.2 ∧ f = g₁ * uv.1 + ell * uv.2

end

end MathlibPlus.Open.ResearchBatch.DiagonalKernels
