import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Claim 20911: the occupied unordered quadratic pair-card feature.  The
source leaves the card inventory and the host-graph representation abstract;
`counts` therefore supplies the exact card-type count for each host `G`. -/
def quadraticPairCardFeature
    {Card Host : Type*} [DecidableEq Card]
    (counts : Host → Card → ℕ) (G : Host) (F B : Card) : ℕ :=
  if F ≠ B then counts G F * counts G B
  else counts G F * (counts G F - 1)

end MathlibPlus.Combinatorics
