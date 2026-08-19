import MathlibPlus.Open.ResearchFormalization.R0990.Claim27995

namespace MathlibPlus.Open.ResearchFormalization.R2733LinearShadowSearch

noncomputable section

open MathlibPlus.Open.ResearchFormalization.CyclicSevenSquared
open MathlibPlus.Open.ResearchFormalization.R0990

/-- Claim 42456: the exact finite linear shadow has 2016 matrices and its
induced action is on the 24 inverse-pair atoms. -/
def exactLinearShadowSearch_claim42456 : Prop :=
  let Atom := {S : Finset V7 // S ∈ inversePairAtoms}
  ∃ action : GL2_7 → Equiv.Perm Atom,
    (∀ M : GL2_7, ∀ S : Atom,
      (action M S).1 = glImage M S.1) ∧
    Fintype.card GL2_7 = 2016 ∧
    Nat.card Atom = 24

end

end MathlibPlus.Open.ResearchFormalization.R2733LinearShadowSearch
