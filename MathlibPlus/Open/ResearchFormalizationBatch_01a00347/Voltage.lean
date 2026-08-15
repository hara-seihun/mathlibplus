import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Voltage

noncomputable section

/-- The prime-voltage lift of a permutation and a voltage function. -/
def primeVoltageLift {B : Type*} {p : ℕ}
    (r : Equiv.Perm B) (β : B → ZMod p) : ZMod p × B → ZMod p × B :=
  fun zb => (zb.1 + β zb.2, r zb.2)

/-- Each lifted generator acts on `𝔽_p × B` by the stated voltage formula. -/
def claim6048 : Prop :=
  ∀ {B I : Type*} [Fintype B] (p : ℕ), Nat.Prime p →
    ∀ (r : I → Equiv.Perm B) (β : I → B → ZMod p) (i : I) (z : ZMod p) (b : B),
      primeVoltageLift (r i) (β i) (z, b) = (z + β i b, r i b)

end

end MathlibPlus.Open.ResearchFormalization.Voltage
