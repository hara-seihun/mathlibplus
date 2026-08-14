import Mathlib

noncomputable section

namespace MathlibPlus.Open.GraphTheory.HeisenbergBatch

abbrev Vp (p : ℕ) := (ZMod p × ZMod p) × ZMod p

def deltaAction (p : ℕ) (u x : Vp p) : Vp p :=
  ((x.1.1,
      x.1.2 + 2 * x.1.1 * u.1.1),
    x.2 + u.1.1 * x.1.2 - u.1.1 * x.1.1 ^ 2 + x.1.1 * u.1.2)

def hZeroOrbit (p : ℕ) (x y : Vp p) : Prop :=
  Relation.ReflTransGen
    (fun a b : Vp p => ∃ u : Vp p, b = deltaAction p u a) x y

/-- Claim 53729: the displayed point-stabilizer action and its three orbit
regimes are stated on the explicit three-coordinate finite-field carrier. -/
def pointStabilizerOrbitClassification_claim53729 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 2 < p →
    ∀ x y : Vp p,
      hZeroOrbit p x y ↔
        (x.1.1 ≠ 0 ∧ y.1.1 = x.1.1) ∨
        (x.1.1 = 0 ∧ x.1.2 ≠ 0 ∧
          y.1.1 = 0 ∧ y.1.2 = x.1.2) ∨
        (x.1.1 = 0 ∧ x.1.2 = 0 ∧ y = x)

end MathlibPlus.Open.GraphTheory.HeisenbergBatch
