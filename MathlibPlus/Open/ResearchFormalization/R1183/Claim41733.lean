-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib
import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.ResearchFormalization.R1183.Claim41733

noncomputable section

abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
abbrev State := Equiv.Perm C7

/-- The shifted relative derivative used in the point-label compatibility
criterion. -/
def shiftedRelativeDerivative_claim41733
    (r : C7) (δ : State) : C7 → C7 :=
  fun s => δ (r + s) - δ r

/-- A family of normalized point-permutation states. -/
def normalizedStateFamily_claim41733
    (δ : C7 → State) : Prop :=
  ∀ y : C7, δ y ∈ MathlibPlus.Combinatorics.Claim41731.normalizedStates

/-- Claim 41733: under the stated support, least-basepoint, and anchor
conditions, this is exactly the point-label derivative compatibility relation. -/
def claim41733
    (X : Set C7) (a : X) (hX : 2 ≤ X.ncard)
    (hleast : ∀ x : X, a.1 ≤ x.1)
    (r : X → C7) (hanchor : r a = 0)
    (δ : C7 → State) : Prop :=
  normalizedStateFamily_claim41733 δ ∧
    ∀ (x x' : X) (y : C7),
      shiftedRelativeDerivative_claim41733 (r x) (δ y) =
        shiftedRelativeDerivative_claim41733 (r x')
          (δ (y + x'.1 - x.1))

end

end MathlibPlus.Open.ResearchFormalization.R1183.Claim41733
