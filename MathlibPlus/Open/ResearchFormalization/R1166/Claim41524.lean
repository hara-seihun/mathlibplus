import MathlibPlus.Open.Algebra.MarkerSupportClaims31768_31769
import MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

namespace MathlibPlus.Open.ResearchFormalization.R1166.Claim41524

open MathlibPlus.Open.Algebra.MarkerSupportClaims
open MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

noncomputable section

/-- No marker strictly above `J` occurs in a polynomial. -/
def noHigherMarker (J : ℕ) (P : MvPolynomial ℕ ℚ) : Prop :=
  ∀ K : ℕ, J < K → MvPolynomial.degreeOf K P = 0

/-- Claim 41524: in the one-largest-marker terminal band, the coefficient
    face of each exact terminal difference contains no marker above `J`. -/
def claim41524 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m r J : ℕ),
    Fintype.card V = m →
      2 ≤ J →
        J ≤ r →
          r < 2 * J →
            firstDifferingTerminalOrder S T R m r →
              hasTotalMarkerOrderAtMost r
                  (terminalComplementTransform S m r) →
                hasTotalMarkerOrderAtMost r
                  (terminalComplementTransform T m r) →
                  hasTotalMarkerOrderAtMost r
                      (terminalComplementTransform R m r) →
                    noHigherMarker J
                        (markerCoefficient J
                          (terminalComplementTransform S m r -
                            terminalComplementTransform T m r)) ∧
                      noHigherMarker J
                        (markerCoefficient J
                          (terminalComplementTransform R m r -
                            terminalComplementTransform T m r))

end

end MathlibPlus.Open.ResearchFormalization.R1166.Claim41524
