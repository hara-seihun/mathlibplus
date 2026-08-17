import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1801

noncomputable section

open TrivSqZeroExt

/-- The coefficient variables `u`, `r`, and `w` over the stated field `F₂`. -/
abbrev Coeff := MvPolynomial (Fin 3) (ZMod 2)
abbrev Poly := Polynomial Coeff
abbrev DualCoeff := DualNumber Coeff
abbrev DualPoly := Polynomial DualCoeff

def u : Coeff := MvPolynomial.X 0

def r : Coeff := MvPolynomial.X 1

def w : Coeff := MvPolynomial.X 2

def s : Coeff := u + r

/-- The one-exponential specialization appearing in the claim. -/
def x (k : ℕ) : DualCoeff :=
  TrivSqZeroExt.inl (u * r ^ (k - 1)) +
    DualNumber.eps * TrivSqZeroExt.inl (w ^ (k - 1))

/-- This is the literal `u r^(k-1) + ε w^(k-1)` expansion, with the
square-zero relation retained as part of the carrier statement. -/
def oneExponentialExpansion : Prop :=
  (DualNumber.eps : DualCoeff) ^ 2 = 0 ∧
    ∀ k : ℕ,
      x k =
        TrivSqZeroExt.inl (u * r ^ (k - 1)) +
          DualNumber.eps * TrivSqZeroExt.inl (w ^ (k - 1))

/-- A rooted tree is represented by its finite rooted child forest. -/
inductive RootedTree : Type
  | node (children : List RootedTree)

mutual
  def order : RootedTree → ℕ
    | .node cs => 1 + forestOrder cs

  def forestOrder : List RootedTree → ℕ
    | [] => 0
    | child :: rest => order child + forestOrder rest
end

mutual
  def factorData : RootedTree → Poly × Poly
    | .node cs =>
        let q := forestData cs
        let h := 1 + forestOrder cs
        (Polynomial.C (u * s ^ (h - 1)) + Polynomial.X * q.1,
          Polynomial.C (u * Polynomial.eval r q.2 + Polynomial.eval w q.1) +
            Polynomial.X * q.2)

  def forestData : List RootedTree → Poly × Poly
    | [] => (1, 0)
    | child :: rest =>
        let q := factorData child
        let q' := forestData rest
        (q.1 * q'.1, q.2 * q'.1 + q.1 * q'.2)
end

def f (R : RootedTree) : Poly := (factorData R).1

def e (R : RootedTree) : Poly := (factorData R).2

def P (R : RootedTree) : Poly := (forestData (match R with | .node cs => cs)).1

def E (R : RootedTree) : Poly := (forestData (match R with | .node cs => cs)).2

/-- The full factor in the dual-number coefficient ring. -/
def liftPoly (q : Poly) : DualPoly :=
  q.map (algebraMap Coeff DualCoeff)

def F (R : RootedTree) : DualPoly :=
  liftPoly (f R) + Polynomial.C DualNumber.eps * liftPoly (e R)

/-- Reversal through a specified degree is the polynomial form of
`z^d q(1/z)`. -/
def reverseAt (d : ℕ) (q : Poly) : Poly :=
  (Finset.range (d + 1)).sum
    (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ (d - i))

def reverseNumerator (R : RootedTree) : PowerSeries Coeff :=
  Polynomial.toPowerSeries (reverseAt (order R - 1) (e R))

def reverseDenominator (R : RootedTree) : PowerSeries Coeff :=
  Polynomial.toPowerSeries (reverseAt (order R) (f R))

/-- The untruncated reverse fraction.  Its denominator has constant term one
under the monicity clause of the source statement. -/
def reverseFraction (R : RootedTree) : PowerSeries Coeff :=
  reverseNumerator R *
    PowerSeries.invOfUnit (reverseDenominator R) (1 : Coeffˣ)

/-- The representative of the reverse signature modulo `z^h`. -/
def Lambda (R : RootedTree) : Poly :=
  PowerSeries.trunc (order R) (reverseFraction R)

def W (R : RootedTree) : ℕ := order R - 1

def rootedFactorShape (R : RootedTree) : Prop :=
  (f R).Monic ∧
    (f R).natDegree = order R ∧
      (e R).degree ≤ ((order R - 1 : ℕ) : WithBot ℕ)

def claim32399 : Prop :=
  oneExponentialExpansion ∧
    ∀ R : RootedTree,
      rootedFactorShape R ∧
        F R = liftPoly (f R) + Polynomial.C DualNumber.eps * liftPoly (e R) ∧
        Lambda R =
          PowerSeries.trunc (order R)
            (reverseNumerator R *
              PowerSeries.invOfUnit (reverseDenominator R) (1 : Coeffˣ))

/-- The full child fractions used in the signature recursion.  In contrast to
`Lambda`, this retains every coefficient of each child fraction until the
single final truncation at the parent order. -/
def childFractionSum (R : RootedTree) : PowerSeries Coeff :=
  match R with
  | .node cs => cs.foldr (fun child acc => reverseFraction child + acc) 0

def parentCorrection (R : RootedTree) : PowerSeries Coeff :=
  PowerSeries.C
      (u * Polynomial.eval r (E R) + Polynomial.eval w (P R)) *
    PowerSeries.X ^ W R

def recursionAtRoot (R : RootedTree) : Prop :=
  f R = Polynomial.C (u * s ^ (order R - 1)) + Polynomial.X * P R ∧
    e R =
      Polynomial.C (u * Polynomial.eval r (E R) + Polynomial.eval w (P R)) +
        Polynomial.X * E R

/-- The exact root recursion and the reverse-signature recursion.  The sum in
`childFractionSum` is formed from the fully expanded child fractions before
`PowerSeries.trunc` is applied. -/
def claim32401 : Prop :=
  ∀ R : RootedTree,
    recursionAtRoot R ∧
      Lambda R =
        PowerSeries.trunc (W R + 1)
          (childFractionSum R + parentCorrection R)

end
end MathlibPlus.Open.ResearchFormalization.R1801
