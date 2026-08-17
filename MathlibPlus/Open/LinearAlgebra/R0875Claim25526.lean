import MathlibPlus.Open.LinearAlgebra.R0875Claim25527

namespace MathlibPlus.Open.LinearAlgebra.R0875Claim25526

noncomputable section
open scoped BigOperators
open Classical

/-- The coefficient transport relation on every actual incidence edge. -/
def coefficientTransport {K R E : Type*} [Field K]
    [Fintype R] [Fintype E] [DecidableEq E]
    (support : R → Finset E) (coeff c : R → E → K)
    (t : R → K) (s : E → K) : Prop :=
  (∀ α, t α ≠ 0) ∧
    (∀ e, s e ≠ 0) ∧
    (∀ α e, e ∈ support α →
      s e * coeff α e = t α * c α e)

/-- Claim 25526: for the rooted fundamental-cycle realization of a finite
forest relation system, nonzero row and edge scalars transport every displayed
relation coefficient to its corresponding cycle coefficient.  The existential
is global, so isolated coordinates and an empty relation family still require
nonzero edge scalars. -/
def coefficientTransportNoHolonomy_claim25526 : Prop :=
  ∀ {K R E V : Type*} [Field K]
    [Fintype R] [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq V]
    (support : R → Finset E) (coeff c : R → E → K)
    (src tgt : E → V) (roots : Set V),
    MathlibPlus.Open.LinearAlgebra.R0875Claim25527.fundamentalCycleRealization
        support coeff c src tgt roots →
      ∃ (t : R → K) (s : E → K),
        coefficientTransport support coeff c t s

end

end MathlibPlus.Open.LinearAlgebra.R0875Claim25526
