import Mathlib
import MathlibPlus.Open.Research.GeneratedGroupExact

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim38254ValuationCode

open MathlibPlus.Open.Research.GeneratedGroupExact

private abbrev F2 := ZMod 2

private def valuationIdeal : Ideal (Polynomial F2) :=
  Ideal.span ({(Polynomial.X + 1) ^ 8} : Set (Polynomial F2))

abbrev QuotientRing := Polynomial F2 ⧸ valuationIdeal

private def maskPolynomial (mu : Mask) : Polynomial F2 :=
  ∑ j : Block, Polynomial.C (mu j) * Polynomial.X ^ j.val

private def maskClass (mu : Mask) : QuotientRing :=
  Ideal.Quotient.mk valuationIdeal (maskPolynomial mu)

private def quotientPower (v : ℕ) : QuotientRing :=
  Ideal.Quotient.mk valuationIdeal ((Polynomial.X + 1) ^ v)

private def powerIdeal (v : ℕ) : Ideal QuotientRing :=
  Ideal.span ({quotientPower v} : Set QuotientRing)

private def codeIdeal (mu : Mask) : Ideal QuotientRing :=
  Ideal.span
    (Set.range (fun k : Fin 8 =>
      maskClass (shiftIter k (signGenerator mu))))

private def hasValuation (mu : Mask) (v : ℕ) : Prop :=
  v ≤ 6 ∧
    ∃ p : Polynomial F2,
      maskClass mu =
          Ideal.Quotient.mk valuationIdeal
            ((Polynomial.X + 1) ^ v * p) ∧
        Polynomial.eval 1 p ≠ 0

/-- Claim 38254: in the explicit eight-coordinate mask carrier, the
polynomial quotient has the stated `(z+1)` relation and all-one class.  A
nonconstant mask of valuation `v ≤ 6` has exactly the shifted-sign code ideal
`((z+1)^(v+1))`; adding the all-one mask preserves that valuation, and neither
mask lies in the code. -/
def claim38254 : Prop :=
  Function.Bijective maskClass ∧
    Polynomial.X ^ 8 - (1 : Polynomial F2) =
      (Polynomial.X + 1) ^ 8 ∧
    maskClass (constantVector 1) = quotientPower 7 ∧
      ∀ (mu : Mask) (v : ℕ),
        ¬ constantMask mu →
          hasValuation mu v →
            hasValuation (maskAdd mu (constantVector 1)) v ∧
              codeIdeal mu = powerIdeal (v + 1) ∧
              (∀ ν : Mask,
                ν ∈ generatedSignCode mu ↔
                  maskClass ν ∈ codeIdeal mu) ∧
              mu ∉ generatedSignCode mu ∧
                maskAdd mu (constantVector 1) ∉ generatedSignCode mu

end MathlibPlus.Open.ResearchFormalization.Claim38254ValuationCode
