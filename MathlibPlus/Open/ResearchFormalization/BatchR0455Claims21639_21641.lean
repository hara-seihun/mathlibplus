import Mathlib
import MathlibPlus.Open.AdmittedBatch.Lehmer
import MathlibPlus.Open.Research.FormalizationBatch.R0455

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0455Claims21639_21641

noncomputable section

private noncomputable def integerPolynomialModTwo
    (p : Polynomial ℤ) : Polynomial (ZMod 2) :=
  p.map (Int.castRingHom (ZMod 2))

private noncomputable def lehmerModTwo : Polynomial (ZMod 2) :=
  integerPolynomialModTwo MathlibPlus.Open.AdmittedBatch.lehmerPolynomial

private noncomputable def packetCompletingCompanion
    (Q : Polynomial ℤ) : Prop :=
  Q.Monic ∧
    MathlibPlus.Open.ResearchFormalizationBatch.rootOrderPacketComplete
      (integerPolynomialModTwo
        (MathlibPlus.Open.AdmittedBatch.lehmerPolynomial * Q))

private noncomputable def packetQuotient : Polynomial (ZMod 2) :=
  integerPolynomialModTwo (Polynomial.cyclotomic 31 ℤ) / lehmerModTwo

private noncomputable def geometricPacket31 : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range 31, (Polynomial.X : Polynomial (ZMod 2)) ^ i

/-- Claim 21639: every monic integer companion whose product with Lehmer's
polynomial is packet-complete over `F₂` has degree at least twenty. -/
def claim21639_packetCompanionDegreeLowerBound : Prop :=
  ∀ Q : Polynomial ℤ,
    packetCompletingCompanion Q →
      20 ≤ Q.natDegree

/-- Claim 21640: under the exact monic, degree-twenty packet-completion item,
the companion reduction is the quotient of the full order-31 packet by
Lehmer's reduction, and the product is the degree-thirty geometric packet. -/
def claim21640_degreeTwentyCompanionReduction : Prop :=
  ∀ Q : Polynomial ℤ,
    packetCompletingCompanion Q →
    Q.natDegree = 20 →
      integerPolynomialModTwo Q = packetQuotient ∧
        integerPolynomialModTwo
            (MathlibPlus.Open.AdmittedBatch.lehmerPolynomial * Q) =
          geometricPacket31

/-- Claim 21641: every monic degree-twenty packet-completing companion has
no positive-index integer cyclotomic divisor. -/
def claim21641_minimumCompanionCyclotomicFree : Prop :=
  ∀ Q : Polynomial ℤ,
    packetCompletingCompanion Q →
    Q.natDegree = 20 →
      ∀ m : ℕ, 0 < m →
        ¬ Polynomial.cyclotomic m ℤ ∣ Q

end

end MathlibPlus.Open.ResearchFormalization.BatchR0455Claims21639_21641
