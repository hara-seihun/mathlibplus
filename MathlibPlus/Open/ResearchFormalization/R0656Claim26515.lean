import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0656Claim26515

noncomputable section

abbrev PairCarrier26515 := MvPolynomial (Fin 2 × Fin 2) ℚ
abbrev TripleCarrier26515 := MvPolynomial (Fin 3 × Fin 2) ℚ

private def sPair26515 (i : Fin 2) : PairCarrier26515 :=
  MvPolynomial.X (i, 0)

private def ePair26515 (i : Fin 2) : PairCarrier26515 :=
  MvPolynomial.X (i, 1)

private def qPair26515 (i : Fin 2) : PairCarrier26515 :=
  ePair26515 i - sPair26515 i ^ 2

private def sTriple26515 (i : Fin 3) : TripleCarrier26515 :=
  MvPolynomial.X (i, 0)

private def eTriple26515 (i : Fin 3) : TripleCarrier26515 :=
  MvPolynomial.X (i, 1)

private def qTriple26515 (i : Fin 3) : TripleCarrier26515 :=
  eTriple26515 i - sTriple26515 i ^ 2

/-- The displayed degree-two coproduct of q at scalar alpha. -/
def deltaQ26515 (α : ℚ) : PairCarrier26515 :=
  qPair26515 0 + qPair26515 1 + MvPolynomial.C α * sPair26515 0 * sPair26515 1

/-- Primitivity of q for the displayed coproduct, on the concrete polynomial
carrier rather than by a scalar alias. -/
def qPrimitive26515 (α : ℚ) : Prop :=
  deltaQ26515 α = qPair26515 0 + qPair26515 1

/-- The isolated pure q tensor q correction. -/
def isolatedCorrection26515 : PairCarrier26515 :=
  qPair26515 0 * qPair26515 1

/-- The two expanded sides of the cobar calculation for q tensor q. -/
def leftCobarTerm26515 (α : ℚ) : TripleCarrier26515 :=
  qTriple26515 0 * qTriple26515 2 +
    qTriple26515 1 * qTriple26515 2 +
      MvPolynomial.C α * sTriple26515 0 * sTriple26515 1 * qTriple26515 2

def rightCobarTerm26515 (α : ℚ) : TripleCarrier26515 :=
  qTriple26515 0 * qTriple26515 1 +
    qTriple26515 0 * qTriple26515 2 +
      MvPolynomial.C α * qTriple26515 0 * sTriple26515 1 * sTriple26515 2

/-- The reduced cobar defect, including the two endpoint correction terms. -/
def cobarDefect26515 (α : ℚ) : TripleCarrier26515 :=
  leftCobarTerm26515 α - rightCobarTerm26515 α +
    qTriple26515 0 * qTriple26515 1 -
      qTriple26515 1 * qTriple26515 2

/-- Claim 26515: the isolated q tensor q correction has exactly the displayed
alpha defect; it is coassociative precisely at alpha zero, equivalently when q
is primitive, and the classical alpha=-1 value cannot be repaired by this
isolated term. -/
def claim26515 : Prop :=
  isolatedCorrection26515 ≠ 0 ∧
    (∀ α : ℚ,
      cobarDefect26515 α =
        MvPolynomial.C α *
          (sTriple26515 0 * sTriple26515 1 * qTriple26515 2 -
            qTriple26515 0 * sTriple26515 1 * sTriple26515 2) ∧
        (cobarDefect26515 α = 0 ↔ α = 0) ∧
        (qPrimitive26515 α ↔ α = 0)) ∧
    cobarDefect26515 (-1) ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.R0656Claim26515
