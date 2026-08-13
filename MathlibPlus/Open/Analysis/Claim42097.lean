import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Faithful countermodel registry node for the incidence-only limitation.
The C₄ construction, transitivity, inverse-paired log-moduli, and Mahler
predicates are explicit source interfaces; the displayed incidence equation
is retained literally over naturals. -/
def incidenceOnlyCannotForceOverlapThresholdGap_claim42097 : Prop :=
  ∃ (Model : Type*) (c₄ : Model)
    (transitive inversePairedLogModuli strictMahlerInflation mahlerFixedPoint :
      Model → Prop)
    (overlap : Model → ℕ) (n v m r : ℕ),
    1 < r ∧
    n * r = m * v ∧
    transitive c₄ ∧
    inversePairedLogModuli c₄ ∧
    overlap c₄ = r ∧
    mahlerFixedPoint c₄ ∧
    ¬ strictMahlerInflation c₄

end MathlibPlus.Open.Analysis
