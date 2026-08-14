import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

def integerPolynomialModTwo (p : Polynomial ℤ) : Polynomial (ZMod 2) :=
  p.map (Int.castRingHom (ZMod 2))

abbrev PositiveCyclotomicIndex := {m : ℕ // 0 < m}

def cyclotomicProductModTwo
    (indices : Multiset PositiveCyclotomicIndex) : Polynomial (ZMod 2) :=
  (indices.map
      (fun m => integerPolynomialModTwo (Polynomial.cyclotomic m.1 ℤ))).prod

/-- Packet completeness is characterized by products of reduced cyclotomic polynomials. -/
def packetCriterionEqualsCyclotomicProductReduction : Prop :=
  ∀ (h : Polynomial (ZMod 2)),
    h.Monic →
    h.eval 0 = 1 →
      ((∃ indices : Multiset PositiveCyclotomicIndex,
          h = cyclotomicProductModTwo indices) ↔
        rootOrderPacketComplete h)

end

end MathlibPlus.Open.ResearchFormalizationBatch
