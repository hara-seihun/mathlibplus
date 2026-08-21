-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Open.Combinatorics.R1183ExactCensus

namespace MathlibPlus.Open.Combinatorics.R1183ExactCensusClaims

/-- Claim 41736 uses the reviewed R-1183 exact census carrier. -/
def claim_41736 : Prop :=
  MathlibPlus.Open.Combinatorics.R1183ExactCensus.claim_31969

/-- Claim 41737 uses the reviewed R-1183 exact support-size census carrier. -/
def claim_41737 : Prop :=
  MathlibPlus.Open.Combinatorics.R1183ExactCensus.claim_31970

/-- Claim 41738 uses the reviewed R-1183 exact complete census carrier. -/
def claim_41738 : Prop :=
  MathlibPlus.Open.Combinatorics.R1183ExactCensus.claim_31971

end MathlibPlus.Open.Combinatorics.R1183ExactCensusClaims
