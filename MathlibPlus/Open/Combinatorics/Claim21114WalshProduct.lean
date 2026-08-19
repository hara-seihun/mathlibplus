import Mathlib

open scoped symmDiff
noncomputable section

namespace MathlibPlus.Open.Combinatorics.Claim21114WalshProduct

def walshCharacter {ι : Type*} [DecidableEq ι]
    (A x : Finset ι) : ℤ :=
  (-1) ^ (A ∩ x).card

/-- Claim 21114: labelled Boolean Walsh characters multiply by symmetric
 difference of their edge-label sets. -/
def claim21114_walshCharacterProductLaw : Prop :=
  ∀ {ι : Type*} [DecidableEq ι]
    (A B x : Finset ι),
    walshCharacter A x * walshCharacter B x =
      walshCharacter (A ∆ B) x

end MathlibPlus.Open.Combinatorics.Claim21114WalshProduct
