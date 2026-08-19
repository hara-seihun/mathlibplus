import MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

namespace MathlibPlus.Open.ResearchFormalization.R1166.Claim31765

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

/-- A nonconstant irreducible factor carried entirely by the strict
lower-marker ring. -/
def strictLowerContentFactor {J : ℕ} (h : StrictLowerRing J) : Prop :=
  ∃ q : StrictLowerRing J,
    Irreducible q ∧
      ¬ IsUnit q ∧
        q ∣ h ∧
          strictLowerMarker J ((strictLowerEmbedding J) q)

/-- The strict-lower-content exit for the two exact terminal quotients. -/
def strictLowerContentExit {J : ℕ}
    (hS hR : StrictLowerRing J) : Prop :=
  (hS ≠ 0 ∧ ¬ IsUnit hS ∧ strictLowerContentFactor hS) ∨
    (hR ≠ 0 ∧ ¬ IsUnit hR ∧ strictLowerContentFactor hR)

/-- The affine, repeated, or strict-lower-content alternatives for exact
terminal forest transforms in the one-largest-marker band. -/
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

/-- Claim 31765: under the exact terminal-transform, common-prime, and
quotient context, the band `J ≤ r_* < 2J` ends in a rational affine terminal
aggregate (including the repeated-transform case) or in strict lower-marker
content. -/
def oneJBlockAffineOrContentDichotomy_claim31765 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m r J : ℕ)
    (p : MarkerRing) (hS hR : StrictLowerRing J),
    terminalUnitQuotientContext S T R m r J p hS hR →
      oneMarkerBandAffineOrContentExit S T R m r J p hS hR

end

end MathlibPlus.Open.ResearchFormalization.R1166.Claim31765
