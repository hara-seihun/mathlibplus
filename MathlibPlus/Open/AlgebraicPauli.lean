import Mathlib

namespace MathlibPlus.Open.AlgebraicPauli

noncomputable section

abbrev EndC := Matrix (Fin 2) (Fin 2) ℂ

def one : EndC := 1

def X : EndC := !![0, 1; 1, 0]

def iY : EndC := !![0, 1; -1, 0]

def Z : EndC := !![1, 0; 0, -1]

def Pminus : EndC := (2 : ℂ)⁻¹ • (one - Z)

def E01 : EndC := !![0, 1; 0, 0]

def E10 : EndC := !![0, 0; 1, 0]

def E11 : EndC := !![0, 0; 0, 1]

def pauli : Fin 4 → EndC := ![one, X, iY, Z]

def R_h (B : EndC) : EndC := X * B

def R_c (B : EndC) : EndC := B * X

def D (B : EndC) : EndC := X * B * X

def rightP (B : EndC) : EndC := B * Pminus

def e11 (B : EndC) : ℂ := B 0 0

/-- The four coefficient matrices are the stated arithmetic Pauli basis. -/
def claim11783 : Prop :=
  LinearIndependent ℂ pauli ∧
    Submodule.span ℂ (Set.range pauli) = ⊤ ∧
    X * X = one ∧
    Z * Z = one ∧
    iY * iY = -one ∧
    Z * X = iY ∧
    X * Z = -iY ∧
    Z * X - X * Z = (2 : ℂ) • iY

/-- Left and right multiplication by the flip give the formal involutions. -/
def claim11784 : Prop :=
  Function.Involutive R_h ∧
    Function.Involutive R_c ∧
    (∀ B : EndC, R_h (R_c B) = R_c (R_h B)) ∧
    (∀ B : EndC, R_h (R_c B) = D B) ∧
    {B : EndC | D B = B} =
      {B : EndC | ∃ a b : ℂ, B = a • one + b • X} ∧
    {B : EndC | D B = -B} =
      {B : EndC | ∃ a b : ℂ, B = a • Z + b • iY}

/-- The one-sided cusp-column map and its rank-one scalar coordinate. -/
def claim11785 : Prop :=
  rightP one = Pminus ∧
    rightP Z = -Pminus ∧
    rightP X = E01 ∧
    rightP iY = E01 ∧
    {B : EndC | rightP B = 0} =
      {B : EndC | ∃ a b : ℂ, B = a • (one + Z) + b • (X - iY)} ∧
    Set.range rightP =
      {B : EndC | ∃ a b : ℂ, B = a • Pminus + b • E01} ∧
    Set.range e11 = Set.univ ∧
    {B : EndC | e11 B = 0} =
      {B : EndC | ∃ a b c : ℂ, B = a • E01 + b • E10 + c • E11}

end

end MathlibPlus.Open.AlgebraicPauli
