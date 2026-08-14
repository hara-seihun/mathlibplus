import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0136

open scoped BigOperators Classical
noncomputable section

def linearitySet {H : Type*} [AddCommGroup H]
    (b : H → ZMod 2) : Set H :=
  {x | ∀ u : H, b (x + u) = b x + b u}

def claim_5829 {H : Type*} [AddCommGroup H]
    (b : H → ZMod 2) (L : Set H) : Prop :=
  L = linearitySet b

def claim_5830 {H : Type*} [AddCommGroup H]
    (b : H → ZMod 2) : Prop :=
  b 0 = 0 →
    ∃ L : AddSubgroup H, L.carrier = linearitySet b ∧
      ∃ χ : L →+ ZMod 2, ∀ x : L, χ x = b x.1

end

end MathlibPlus.Open.ResearchBatch.D0136
