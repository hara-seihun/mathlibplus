import Mathlib

namespace MathlibPlus.Open.Algebra.PathSwitchM0

noncomputable section

/-- Positive indices label the variables `x_i` occurring in partition monomials. -/
abbrev Positive := {n : ℕ // 0 < n}

abbrev PathRing := MvPolynomial (Option Positive) ℤ

private def positiveOne : Positive := ⟨1, by decide⟩
private def positiveTwo : Positive := ⟨2, by decide⟩
private def positiveThree : Positive := ⟨3, by decide⟩

def xVar (i : Positive) : PathRing := MvPolynomial.X (some i)

def zVar : PathRing := MvPolynomial.X none

/-- The monomial `x_λ`, for a partition represented by its positive parts. -/
def xLambda (part : Multiset Positive) : PathRing :=
  (part.map xVar).prod

def shiftedPositive (s : Positive) (a : ℕ) : Positive :=
  ⟨a + s.1, by omega⟩

/-- Coefficientwise extension of the prescribed action on monomial markers. -/
def phiCoeffs (s : Positive) (p : PathRing) :
    (Option Positive →₀ ℕ) →₀ ℤ :=
  (AddMonoidAlgebra.coeff p).sum (fun m c =>
    Finsupp.single
      (Finsupp.erase none m +
        Finsupp.single (some (shiftedPositive s (m none))) 1) c)

def Phi (s : Positive) (p : PathRing) : PathRing :=
  AddMonoidAlgebra.ofCoeff (phiCoeffs s p)

def A (p : PathRing) : PathRing := Phi positiveOne p

def P : PathRing :=
  xVar positiveOne ^ 2 + xVar positiveTwo +
    zVar * (xVar positiveOne + zVar)

def Q : PathRing := (xVar positiveOne + zVar) ^ 2

def D : PathRing := P - Q

def L : PathRing := xVar positiveOne + zVar

def commonValue : PathRing :=
  xVar positiveOne ^ 3 + 2 * (xVar positiveOne * xVar positiveTwo) +
    xVar positiveThree

/-- The factorisation assertion tested by the `m=0` path-switch instance. -/
def pathSwitchM0 : Prop := A (L * D) = A D * A P

/-- The exact three-vertex path calculation, including the non-factorisation. -/
def claim_60553 : Prop :=
  (∀ (s : Positive) (u v : PathRing),
    Phi s (u + v) = Phi s u + Phi s v) ∧
  (∀ (s : Positive) (c : ℤ) (u : PathRing),
    Phi s (c • u) = c • Phi s u) ∧
  (∀ (s : Positive) (a : ℕ) (part : Multiset Positive),
    Phi s (zVar ^ a * xLambda part) =
      xVar (shiftedPositive s a) * xLambda part) ∧
  A P = A Q ∧
  A Q = commonValue ∧
  D = xVar positiveTwo - zVar * xVar positiveOne ∧
  L = xVar positiveOne + zVar ∧
  A D = 0 ∧
  A (L * D) = xVar positiveTwo ^ 2 -
    xVar positiveOne * xVar positiveThree ∧
  A (L * D) ≠ A D * A P ∧
  A D * A P = 0 ∧
  ¬ pathSwitchM0

end
end MathlibPlus.Open.Algebra.PathSwitchM0
