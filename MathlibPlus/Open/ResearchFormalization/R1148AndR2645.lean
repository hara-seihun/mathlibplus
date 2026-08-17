import MathlibPlus.Open.ResearchFormalizationBatch_019ffee2

namespace MathlibPlus.Open.ResearchFormalization.R1148AndR2645

noncomputable section

private def reciprocalUnitCyclotomicFamily : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let P := Polynomial.cyclotomic (3 ^ k) ℤ
    P.Monic ∧ P.reverse = P ∧ P.coeff 0 = 1

/-- Claim 42125: reciprocal/unit structure does not prevent the displayed
3-power cyclotomic family from eventually avoiding every fixed finite local
field. -/
def reciprocityUnitDoesNotForceBoundedLocalClustering_claim42125 : Prop :=
  reciprocalUnitCyclotomicFamily ∧
    MathlibPlus.Open.claim_42123

end

end MathlibPlus.Open.ResearchFormalization.R1148AndR2645
