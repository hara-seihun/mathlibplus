import MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

namespace MathlibPlus.Open.ResearchFormalization.R1166.Claim31766

open MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

/-- Claim 31766: in the exact one-marker terminal context, the first
terminal difference is before half the graph order.  The quarter-order
hypothesis places the half-order bound below twice the largest marker, so
the one-marker band feeds the affine or repeated/lower-content exit. -/
def claim31766 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m r J : ℕ)
    (p : MarkerRing) (hS hR : StrictLowerRing J),
    terminalUnitQuotientContext S T R m r J p hS hR →
      (r : ℚ) < (m : ℚ) / 2 ∧
      ((m : ℚ) / 4 ≤ (J : ℚ) →
        (m : ℚ) / 2 ≤ 2 * (J : ℚ) ∧
          J ≤ r ∧ r < 2 * J ∧
          ((hS = 0 ∨ hR = 0) ∨
            (hS ≠ 0 ∧ hR ≠ 0 ∧ IsUnit hS ∧ IsUnit hR) →
              (((hS = 0 ∨ hR = 0) ∧
                  repeatedTerminalTransform
                    (terminalComplementTransform T m r)
                    (terminalComplementTransform S m r)
                    (terminalComplementTransform R m r)) ∨
                (hS ≠ 0 ∧ hR ≠ 0 ∧ IsUnit hS ∧ IsUnit hR ∧
                  rationalAffineTerminalLine
                    (terminalComplementTransform T m r)
                    (terminalComplementTransform S m r)
                    (terminalComplementTransform R m r) p))))

end MathlibPlus.Open.ResearchFormalization.R1166.Claim31766
