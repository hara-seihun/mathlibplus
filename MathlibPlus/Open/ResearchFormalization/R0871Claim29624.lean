import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0871Claim29624

noncomputable section

abbrev BinaryPolynomial := MvPolynomial (Fin 2) ℚ

def scalar (lam : ℚ) : BinaryPolynomial :=
  (algebraMap ℚ BinaryPolynomial) lam

def binaryTangentTriple
    (lam : ℚ) (X Y Z : BinaryPolynomial)
    (a b c : BinaryPolynomial) : Prop :=
  a * Y ^ 2 - scalar lam * b * X ^ 2 + c * Z ^ 2 = 0

def binaryCore
    (lam : ℚ) (X Y Z : BinaryPolynomial) : Prop :=
  lam ≠ 0 ∧
    lam ≠ 1 ∧
    X ≠ 0 ∧
    Y ≠ 0 ∧
    Z ≠ 0 ∧
    Z = scalar lam * X - Y ∧
    IsCoprime X Y ∧
    IsCoprime X Z ∧
    IsCoprime Y Z

def channelRepresentation
    (lam : ℚ) (X Y : BinaryPolynomial)
    (P Q a b c : BinaryPolynomial) : Prop :=
  c = P * X + Q * Y ∧
    a = -P * X + Q * (2 * scalar lam * X - Y) ∧
    b = P * (scalar lam * X - 2 * Y) + scalar lam * Q * Y

/-- Claim 29624: the binary tangent syzygy has exactly the two displayed
quotient channels, and every pair of channels produces a tangent triple. -/
def claim29624 : Prop :=
  ∀ (lam : ℚ) (X Y Z : BinaryPolynomial),
    binaryCore lam X Y Z →
      (∀ (a b c : BinaryPolynomial),
        binaryTangentTriple lam X Y Z a b c →
          ∃! pq : BinaryPolynomial × BinaryPolynomial,
            channelRepresentation lam X Y pq.1 pq.2 a b c) ∧
      (∀ (P Q : BinaryPolynomial),
        binaryTangentTriple lam X Y Z
          (-P * X + Q * (2 * scalar lam * X - Y))
          (P * (scalar lam * X - 2 * Y) + scalar lam * Q * Y)
          (P * X + Q * Y))

end

end MathlibPlus.Open.ResearchFormalization.R0871Claim29624
