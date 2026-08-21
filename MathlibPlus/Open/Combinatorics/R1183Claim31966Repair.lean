-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.Combinatorics.R1183.Claim31966Repair

noncomputable section

open MathlibPlus.Combinatorics.Claim41731

private abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
private abbrev State := Equiv.Perm C7

private def shiftedDerivative (r : C7) (δ : State) : C7 → C7 :=
  fun s => (δ (r + s)) - (δ r)

private def normalizedStateFamily (δ : C7 → State) : Prop :=
  ∀ y : C7, δ y ∈ normalizedStates

private def leastBasepoint (X : Finset C7) (a : C7) : Prop :=
  a ∈ X ∧ ∀ x ∈ X, a ≤ x

private def normalizedSupportOffset (X : Finset C7) (a : C7)
    (r : C7 → C7) : Prop :=
  2 ≤ X.card ∧ leastBasepoint X a ∧ r a = 0

/-- Claim 31966: for a specified support, least basepoint, normalized offset,
and state family, this is the compatibility predicate.  It is a predicate on
`δ`, not a universal assertion that an arbitrary state family is compatible. -/
def pointLabelDerivativeCompatibility31966
    (X : Finset C7) (a : C7) (r : C7 → C7)
    (δ : C7 → State) : Prop :=
  normalizedSupportOffset X a r ∧
    normalizedStateFamily δ ∧
      ∀ x ∈ X, ∀ x' ∈ X, ∀ y : C7,
        shiftedDerivative (r x) (δ y) =
          shiftedDerivative (r x') (δ (y + x' - x))

end

end MathlibPlus.Open.Combinatorics.R1183.Claim31966Repair
