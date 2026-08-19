import MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1166.Claim41530

open MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

/-- A nonconstant irreducible factor carried entirely by the strict
lower-marker ring.  Its strict-lower support records the descent of the
largest marker. -/
def strictLowerContentFactor {J : ℕ} (h : StrictLowerRing J) : Prop :=
  ∃ q : StrictLowerRing J,
    Irreducible q ∧
      ¬IsUnit q ∧
        q ∣ h ∧
          strictLowerMarker J ((strictLowerEmbedding J) q)

/-- The lower-content exit is the occurrence of such a factor in a nonzero
nonunit quotient, rather than merely the hypothesis that a quotient is a
nonunit. -/
def strictLowerContentExit {J : ℕ}
    (hS hR : StrictLowerRing J) : Prop :=
  (hS ≠ 0 ∧ ¬IsUnit hS ∧ strictLowerContentFactor hS) ∨
    (hR ≠ 0 ∧ ¬IsUnit hR ∧ strictLowerContentFactor hR)

/-- The affine, repeated, or strict-lower-content alternatives at the exact
terminal order and with the exact quotient data of the one-marker context. -/
def oneMarkerBandAffineOrContentExit {V : Type*} [Fintype V]
    [DecidableEq V]
    (S T R : SimpleGraph V) (m r J : ℕ)
    (p : MarkerRing) (hS hR : StrictLowerRing J) : Prop :=
  (((hS = 0 ∨ hR = 0) ∧
      repeatedTerminalTransform
        (terminalComplementTransform T m r)
        (terminalComplementTransform S m r)
        (terminalComplementTransform R m r)) ∨
    (hS ≠ 0 ∧ hR ≠ 0 ∧ IsUnit hS ∧ IsUnit hR ∧
      rationalAffineTerminalLine
        (terminalComplementTransform T m r)
        (terminalComplementTransform S m r)
        (terminalComplementTransform R m r) p) ∨
    strictLowerContentExit hS hR)

/-- The one-marker terminal context with the upper band inequality omitted;
that inequality is the conclusion of the quarter-order localization rather
than an assumption. -/
def terminalQuarterOrderContext {V : Type*} [Fintype V]
    [DecidableEq V]
    (S T R : SimpleGraph V) (m r J : ℕ)
    (p : MarkerRing) (hS hR : StrictLowerRing J) : Prop :=
  2 ≤ J ∧
    J ≤ m / 2 ∧
      J ≤ r ∧
        Fintype.card V = m ∧
          firstDifferingTerminalOrder S T R m r ∧
            primitiveLinearPrime J p ∧
              p ∣ terminalComplementTransform S m r -
                terminalComplementTransform T m r ∧
                p ∣ terminalComplementTransform R m r -
                  terminalComplementTransform T m r ∧
                  terminalComplementTransform S m r -
                      terminalComplementTransform T m r =
                    (strictLowerEmbedding J) hS * p ∧
                    terminalComplementTransform R m r -
                        terminalComplementTransform T m r =
                      (strictLowerEmbedding J) hR * p ∧
                      strictLowerMarker J ((strictLowerEmbedding J) hS) ∧
                        strictLowerMarker J ((strictLowerEmbedding J) hR)

/-- Claim 41530: every first differing terminal order is before half the
finite graph order.  If the largest marker is at least quarter order, the
half-order bound gives the one-marker band automatically, and the affine,
repeated, or strict-lower-content exit follows. -/
def claim41530 : Prop :=
  (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m r : ℕ),
    Fintype.card V = m →
      firstDifferingTerminalOrder S T R m r →
        (r : ℚ) < (m : ℚ) / 2) ∧
    (∀ {V : Type*} [Fintype V] [DecidableEq V]
      (S T R : SimpleGraph V) (m r J : ℕ)
      (p : MarkerRing) (hS hR : StrictLowerRing J),
      terminalQuarterOrderContext S T R m r J p hS hR →
        (m : ℚ) / 4 ≤ (J : ℚ) →
          (m : ℚ) / 2 ≤ 2 * (J : ℚ) ∧
            r < 2 * J ∧
              oneMarkerBandAffineOrContentExit S T R m r J p hS hR)

end MathlibPlus.Open.ResearchFormalization.R1166.Claim41530
