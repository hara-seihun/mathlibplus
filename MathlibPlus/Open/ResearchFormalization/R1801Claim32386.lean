import MathlibPlus.Open.ResearchFormalization.R1801Claim32391

namespace MathlibPlus.Open.ResearchFormalization.R1801Claim32386

open MathlibPlus.Open.ResearchFormalization.R1801
open MathlibPlus.Open.ResearchFormalization.R1801Claim32391

/-- Claim 32386: the displayed leaf-path constructions are rooted trees of
order `n` for every `n ≥ 3`. -/
def claim32386 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    let A := aTree n
    let Q := qTree n
    let B := bTree n
    order A = n ∧ order B = n

end MathlibPlus.Open.ResearchFormalization.R1801Claim32386
