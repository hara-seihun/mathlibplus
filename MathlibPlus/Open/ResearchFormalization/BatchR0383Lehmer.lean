import MathlibPlus.Algebra.Claim20663
import MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460

namespace MathlibPlus.Open.ResearchFormalization.R0383Lehmer

open Polynomial

noncomputable section

/-- Mahler measure of an integer polynomial after complexification. -/
noncomputable def integerMahlerMeasure (P : Polynomial ℤ) : ℝ :=
  Polynomial.mahlerMeasure (P.map (algebraMap ℤ ℂ))

/-- The second noncyclotomic factor in the degree-six equality family, namely
`L(-x)`. -/
noncomputable def lehmerNegative : Polynomial ℤ :=
  MathlibPlus.Algebra.Claim20663.lehmerPolynomial.comp (-Polynomial.X)

/-- The carrier described by “monic reciprocal integer polynomial of degree
16”. -/
def isMonicReciprocalDegree16 (G : Polynomial ℤ) : Prop :=
  G.Monic ∧ G.natDegree = 16 ∧ G.reverse = G

/-- Claim 20664: a nonzero integer polynomial strictly between one and
Lehmer's number has degree at least 56. -/
def claim20664 : Prop :=
  ∀ P : Polynomial ℤ,
    P ≠ 0 →
      1 < integerMahlerMeasure P →
        integerMahlerMeasure P < MathlibPlus.Algebra.Claim20663.lehmerNumber →
          56 ≤ P.natDegree

/-- Claim 20668: the exact degree-16 equality classification. -/
def claim20668 : Prop :=
  ∀ G : Polynomial ℤ,
    isMonicReciprocalDegree16 G →
      (integerMahlerMeasure G = MathlibPlus.Algebra.Claim20663.lehmerNumber ↔
        ∃ C : Polynomial ℤ,
          MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.IsCyclotomicPadding C ∧
            (G = MathlibPlus.Algebra.Claim20663.lehmerPolynomial * C ∨
              G = lehmerNegative * C))

/-- The products obtained by multiplying a degree-six cyclotomic padding by
one of the two displayed Lehmer factors. -/
def lehmerDegree16ProductSet : Set (Polynomial ℤ) :=
  {G | ∃ C : Polynomial ℤ,
    MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.IsCyclotomicPadding C ∧
      (G = MathlibPlus.Algebra.Claim20663.lehmerPolynomial * C ∨
        G = lehmerNegative * C)}

/-- Claim 20671: the 59 paddings and the two distinct displayed factors yield
exactly 118 distinct monic reciprocal degree-16 equality polynomials. -/
def claim20671 : Prop :=
  Set.Finite
      MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.cyclotomicPaddingSet ∧
    MathlibPlus.Open.ResearchFormalization.BatchR0383R0415R0460.cyclotomicPaddingSet.ncard = 59 ∧
    (∀ G : Polynomial ℤ, G ∈ lehmerDegree16ProductSet →
      isMonicReciprocalDegree16 G ∧
        integerMahlerMeasure G = MathlibPlus.Algebra.Claim20663.lehmerNumber) ∧
    Set.Finite lehmerDegree16ProductSet ∧
    lehmerDegree16ProductSet.ncard = 118 ∧
    MathlibPlus.Algebra.Claim20663.lehmerPolynomial ≠ lehmerNegative

end

end MathlibPlus.Open.ResearchFormalization.R0383Lehmer
