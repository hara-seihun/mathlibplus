import MathlibPlus.Open.ResearchFormalizeBatch019ffede

namespace MathlibPlus.Open.ResearchFormalization.R0728

noncomputable section

open MathlibPlus.Open.ResearchFormalizeBatch

private noncomputable def coverCount {V : Type} [Fintype V]
    [PartialOrder V] : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun p : V × V => CovBy p.1 p.2)).card

private def unliftedFlowVariableCount (vertices covers starts : ℕ) : ℕ :=
  vertices * starts + covers * starts

private def liftedFlowVariableCount
    (vertices covers starts K : ℕ) : ℕ :=
  (vertices * starts + covers * starts) * (K + 1)

/-- Claim 24271: the exact binary flow formulations use one assignment and
one cover variable for each allowed start (and, after lifting, each explicit
counter level), so their variable counts have polynomial bounds in the
finite graded-poset data and in K; exactness is the bounded-switch
characterization rather than enumeration of saturated paths. -/
def polynomialSizeExactBinaryFormulation_claim24271 : Prop :=
  ∀ {V State : Type} [Fintype V] [PartialOrder V]
    [DecidableEq State]
    (r K : ℕ) (rank : V → Fin (r + 1)) (σ : V → State),
    let vertices := Fintype.card V
    let covers := coverCount (V := V)
    let starts := r + 1
    let unliftedSize :=
      unliftedFlowVariableCount vertices covers starts
    let liftedSize :=
      liftedFlowVariableCount vertices covers starts K
    let polynomialBase := (vertices + covers + starts + 1) ^ 3
    let liftedFeasible :=
      ∃ z : LiftedAssignment V r K,
        ∃ x : LiftedCoverAssignment V r K,
          liftedCounterFlowFeasible r K rank σ z x
    unliftedSize ≤ polynomialBase ∧
      liftedSize ≤ (K + 1) * polynomialBase ∧
      (liftedFeasible ↔
        boundedSwitchSCD (V := V) (State := State) r K rank σ)

end

end MathlibPlus.Open.ResearchFormalization.R0728
