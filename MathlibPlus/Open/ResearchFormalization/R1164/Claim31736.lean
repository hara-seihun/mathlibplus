import MathlibPlus.Open.ResearchFormalization.R1164FullSuborbit

namespace MathlibPlus.Open.ResearchFormalization.R1164

/-- Claim 31736: no retained displayed transporter belongs to the exact
    two-closure of its generated translation pair; all 50,262 retained rows
    fail the displayed-transporter route. -/
def claim31736 : Prop :=
  r1164RetainedCount = 50262 ∧
    (¬ ∃ r : R1164RetainedRow,
      ¬ r1164DisplayedClosureFailure r) ∧
      ∀ r : R1164RetainedRow, r1164DisplayedClosureFailure r

end MathlibPlus.Open.ResearchFormalization.R1164
