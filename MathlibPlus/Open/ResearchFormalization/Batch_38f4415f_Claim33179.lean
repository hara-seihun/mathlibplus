import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim33179

private def cycleSucc (p : ℕ) (hp : 0 < p) (i : Fin p) : Fin p :=
  ⟨(i.1 + 1) % p, Nat.mod_lt _ hp⟩

private def deltaSecond (p : ℕ) (hp : 0 < p)
    (D : Fin p × Fin p → ZMod p)
    (i j : Fin p) : ZMod p :=
  D (i, cycleSucc p hp j) - D (i, j)

private def deltaFirst (p : ℕ) (hp : 0 < p)
    (E : Fin p × Fin p → ZMod p)
    (i j : Fin p) : ZMod p :=
  E (cycleSucc p hp i, j) - E (i, j)

private def potential (p : ℕ) (hp : 0 < p)
    (D E : Fin p × Fin p → ZMod p)
    (i j : Fin p) : ZMod p :=
  (∑ k : Fin i.1, D (⟨k.1, Nat.lt_trans k.isLt i.isLt⟩, ⟨0, hp⟩)) +
    ∑ ℓ : Fin j.1, E (i, ⟨ℓ.1, Nat.lt_trans ℓ.isLt j.isLt⟩)

/-- A closed, zero-period one-form on the finite torus is the gradient of
    the displayed prefix-sum potential. -/
def claim33179 : Prop :=
  ∀ (p : ℕ) (hpPrime : Nat.Prime p),
    let hp : 0 < p := hpPrime.pos
    ∀ (D E : Fin p × Fin p → ZMod p),
      (∀ i j, deltaSecond p hp D i j = deltaFirst p hp E i j) ∧
      (∀ j : Fin p, ∑ i : Fin p, D (i, j) = 0) ∧
      (∀ i : Fin p, ∑ j : Fin p, E (i, j) = 0) →
      ∀ i j : Fin p,
        potential p hp D E (cycleSucc p hp i) j -
          potential p hp D E i j = D (i, j) ∧
        potential p hp D E i (cycleSucc p hp j) -
          potential p hp D E i j = E (i, j)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim33179
