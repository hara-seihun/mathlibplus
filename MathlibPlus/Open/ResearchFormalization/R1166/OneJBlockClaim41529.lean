import MathlibPlus.Open.ResearchFormalization.R1166.Claim31763
import MathlibPlus.Open.Algebra.MarkerSupportClaims31768_31769

namespace MathlibPlus.Open.ResearchFormalization.R1166.OneJBlockClaim41529

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

abbrev MarkerRing := MathlibPlus.Open.ResearchFormalization.R1166.Claim31763.MarkerRing

/-- The exact all-order support carrier for a terminal forest sum. -/
def exactTerminalForestSupport {V : Type*} [Fintype V]
    [DecidableEq V] (X : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ q : ℕ,
    MathlibPlus.Open.Algebra.MarkerSupportClaims.hasTotalMarkerOrderAtMost q
      (terminalComplementTransform X m q)

/-- The common lower-half irreducible prime and the first terminal
 differences used by the one-`J` block argument. -/
def commonLowerHalfPrime {V : Type*} [Fintype V]
    [DecidableEq V] (S T R : SimpleGraph V) (m J r : ℕ)
    (p : MarkerRing) : Prop :=
  2 ≤ J ∧
    J ≤ m / 2 ∧
      primitiveLinearPrime J p ∧
        firstDifferingTerminalOrder S T R m r ∧
          p ∣ terminalComplementTransform S m r -
            terminalComplementTransform T m r ∧
          p ∣ terminalComplementTransform R m r -
            terminalComplementTransform T m r

/-- A nonzero nonunit irreducible factor wholly supported below `J`. -/
def strictLowerContent (J : ℕ) (hS hR : MarkerRing) : Prop :=
  (hS ≠ 0 ∧
      ∃ d : MarkerRing,
        Irreducible d ∧
          ¬ IsUnit d ∧
            strictLowerMarker J d ∧
              d ∣ hS) ∨
    (hR ≠ 0 ∧
      ∃ d : MarkerRing,
        Irreducible d ∧
          ¬ IsUnit d ∧
            strictLowerMarker J d ∧
              d ∣ hR)

/-- The two exits of the terminal aggregate argument, with repeated
transforms included in the affine/repeated exit. -/
def rationalAffineOrRepeated
    (thetaT thetaS thetaR p : MarkerRing) : Prop :=
  repeatedTerminalTransform thetaT thetaS thetaR ∨
    rationalAffineTerminalLine thetaT thetaS thetaR p

/-- Exact one-`J`-band input, retaining the common lower-half condition on `J`
and the two common-prime divisibilities. -/
def oneJBlockContext {V : Type*} [Fintype V]
    [DecidableEq V] (S T R : SimpleGraph V) (m J r : ℕ)
    (p : MarkerRing) : Prop :=
  J ≤ r ∧
    r < 2 * J ∧
      commonLowerHalfPrime S T R m J r p

/-- Claim 41529: for exact terminal forest sums on finite trees, the
one-`J` band has the rational-affine/repeated aggregate or strict lower-marker
content alternative.  The conclusion also records the all-order support of
all three exact terminal sums, rather than replacing it by an assumed opaque
support premise. -/
def claim41529 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m J r : ℕ) (p : MarkerRing),
    S.IsTree →
      T.IsTree →
        R.IsTree →
          Fintype.card V = m →
            oneJBlockContext S T R m J r p →
              exactTerminalForestSupport S m ∧
                exactTerminalForestSupport T m ∧
                  exactTerminalForestSupport R m ∧
                    ∃ hS hR : MarkerRing,
                      terminalComplementTransform S m r -
                            terminalComplementTransform T m r =
                          hS * p ∧
                        terminalComplementTransform R m r -
                            terminalComplementTransform T m r =
                          hR * p ∧
                        strictLowerMarker J hS ∧
                          strictLowerMarker J hR ∧
                            (rationalAffineOrRepeated
                                (terminalComplementTransform T m r)
                                (terminalComplementTransform S m r)
                                (terminalComplementTransform R m r) p ∨
                              strictLowerContent J hS hR)

end

end MathlibPlus.Open.ResearchFormalization.R1166.OneJBlockClaim41529
