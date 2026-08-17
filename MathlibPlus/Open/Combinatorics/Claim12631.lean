import MathlibPlus.Open.Combinatorics.ComponentTransfer

namespace MathlibPlus.Open.Combinatorics.Claim12631

/-- The prescribed local unit transfer can coexist with a trivial global
component-preserving pairing. -/
def nonzeroUnitTransferDoesNotImplyNongluability : Prop :=
  MathlibPlus.Open.Combinatorics.exactComponentDegreeSignatures ∧
    MathlibPlus.Open.Combinatorics.prescribedMapsCrossSignatureBoundary ∧
    MathlibPlus.Open.Combinatorics.trivialGlobalComponentPairing

end MathlibPlus.Open.Combinatorics.Claim12631
