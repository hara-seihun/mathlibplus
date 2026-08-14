import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- A polynomial over F_2 has uniform divisibility multiplicity within every
root-order packet of monic irreducible factors. -/
def rootOrderPacketComplete (h : Polynomial (ZMod 2)) : Prop :=
  h.Monic ∧
    h.eval 0 = 1 ∧
      ∀ (m : ℕ),
        Odd m →
          ∀ (p q : Polynomial (ZMod 2)),
            p.Monic →
            q.Monic →
            Irreducible p →
            Irreducible q →
            (∀ α : AlgebraicClosure (ZMod 2),
              Polynomial.IsRoot
                (p.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))) α →
                orderOf α = m) →
            (∀ α : AlgebraicClosure (ZMod 2),
              Polynomial.IsRoot
                (q.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))) α →
                orderOf α = m) →
            ∀ k : ℕ, p ^ k ∣ h ↔ q ^ k ∣ h

/-- Packet completeness descends through every positive substitution exponent. -/
def packetCompletenessDescendsUnderSubstitution : Prop :=
  ∀ (h : Polynomial (ZMod 2)) (k : ℕ),
    0 < k →
    rootOrderPacketComplete
      (h.comp ((Polynomial.X : Polynomial (ZMod 2)) ^ k)) →
    rootOrderPacketComplete h

end MathlibPlus.Open.ResearchFormalizationBatch
