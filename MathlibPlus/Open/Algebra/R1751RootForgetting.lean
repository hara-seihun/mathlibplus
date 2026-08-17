import Mathlib

open Classical
open scoped BigOperators

namespace MathlibPlus.Open.Algebra.R1751

noncomputable section

abbrev ShiftMonomial := ℕ × Multiset ℕ
abbrev ShiftTracePoly := AddMonoidAlgebra ℚ ShiftMonomial

def shiftMonomial (s : ℕ) (m : ShiftMonomial) : ShiftMonomial :=
  (0, {m.1 + s} + m.2)

def shiftTrace (s : ℕ) (P : ShiftTracePoly) : ShiftTracePoly :=
  AddMonoidAlgebra.ofCoeff
    ((Finsupp.lmapDomain ℚ ℚ (shiftMonomial s)) P.coeff)

def zMonomial : ShiftTracePoly :=
  AddMonoidAlgebra.single (1, 0) 1

def xMonomial (parts : Multiset ℕ) : ShiftTracePoly :=
  AddMonoidAlgebra.single (0, parts) 1

def rootForget (P : ShiftTracePoly) : ShiftTracePoly :=
  Finset.sum P.coeff.support
    (fun m => P.coeff m • xMonomial ({m.1 + 1} + m.2))

def shiftedSelector (j : ℕ) (H : ShiftTracePoly) : ShiftTracePoly :=
  rootForget (zMonomial ^ j * H)

def genuineFactor (P : ShiftTracePoly) : ShiftTracePoly :=
  zMonomial * P + rootForget (zMonomial * P)

def S₁ : ShiftTracePoly := genuineFactor 1
def S₂ : ShiftTracePoly := genuineFactor S₁
def P₃ : ShiftTracePoly := genuineFactor S₂
def Y₃ : ShiftTracePoly := genuineFactor (S₁ ^ 2)
def U₅ : ShiftTracePoly := genuineFactor (S₁ * P₃)
def V₄ : ShiftTracePoly := genuineFactor Y₃

def secantE : ShiftTracePoly := S₁ * U₅ - S₂ * V₄

def deltaPolynomial : ShiftTracePoly :=
  xMonomial {1, 2, 5} - xMonomial {1, 3, 4} - xMonomial {2, 2, 4} +
    xMonomial {2, 3, 3} + xMonomial {3, 5} - xMonomial {4, 4}

/-- Factor-coprimality: every common factor is a unit.  This is the
factor/gcd notion of coprimality, not comaximality of the two ideals. -/
def FactorCoprime (P Q : ShiftTracePoly) : Prop :=
  ∀ D : ShiftTracePoly, D ∣ P → D ∣ Q → IsUnit D

def homogeneousOfWeight (w : ℕ) (P : ShiftTracePoly) : Prop :=
  ∀ m ∈ P.coeff.support,
    m.1 + m.2.sum = w

/-- A weighted polynomial is monic in its top root state when the coefficient
of its z^w state (with no component variables) is one. -/
def monicTopRootState (w : ℕ) (P : ShiftTracePoly) : Prop :=
  P.coeff (w, 0) = 1

/-- The concrete genuine-product secant, its factor-coprimality, and its two
shifted-selector expansions. -/
def claim_34116 : Prop :=
  secantE ≠ 0 ∧
    FactorCoprime (S₁ * U₅) (S₂ * V₄) ∧
      shiftedSelector 2 secantE = deltaPolynomial ∧
        shiftedSelector 3 secantE = -xMonomial {1} * deltaPolynomial ∧
          deltaPolynomial ≠ 0

/-- The smallest genuine context kills the second shifted row but not the
adjacent row. -/
def claim_34117 : Prop :=
  S₁ = zMonomial + xMonomial {1} ∧
    shiftedSelector 2 (S₁ * secantE) =
      xMonomial {1} * shiftedSelector 2 secantE +
        shiftedSelector 3 secantE ∧
      shiftedSelector 2 (S₁ * secantE) = 0 ∧
        S₁ * secantE ≠ 0 ∧
          shiftedSelector 3 (S₁ * secantE) ≠ 0

/-- The realized counterexample to dropping the heavy-context weight
condition. -/
def claim_34128 : Prop :=
  let C := S₁
  let H := zMonomial * secantE
  homogeneousOfWeight 1 C ∧
    monicTopRootState 1 C ∧
      homogeneousOfWeight 7 H ∧
        H ≠ 0 ∧
          rootForget (zMonomial * C * H) =
              rootForget (zMonomial ^ 2 * S₁ * secantE) ∧
            rootForget (zMonomial ^ 2 * S₁ * secantE) = 0

end

end MathlibPlus.Open.Algebra.R1751
