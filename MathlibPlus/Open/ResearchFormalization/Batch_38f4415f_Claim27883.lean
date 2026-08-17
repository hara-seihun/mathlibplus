import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27883

private abbrev Plane (p : ℕ) := ZMod p × ZMod p
private abbrev Target (p : ℕ) := ZMod p × ZMod p × ZMod p

private def quadraticF (p : ℕ) (u : Plane p) : Target p :=
  (u.1 * (u.1 - 1), ((2 : ZMod p) * u.1 - 1) * u.2, u.2 ^ 2)

private def polarDerivative (p : ℕ) (u c : Plane p) : Target p :=
  quadraticF p (u + c) - quadraticF p u - quadraticF p c

private def displacementPlane (p : ℕ) (u : Plane p) :
    Submodule (ZMod p) (Target p) :=
  Submodule.span (ZMod p)
    ({(u.1, u.2, 0), (0, u.1, u.2)} : Set (Target p))

private def isLinearPolarDerivative (p : ℕ) (u : Plane p) : Prop :=
  (∀ c d : Plane p,
    polarDerivative p u (c + d) =
      polarDerivative p u c + polarDerivative p u d) ∧
    (∀ a : ZMod p, ∀ c : Plane p,
      polarDerivative p u (a • c) = a • polarDerivative p u c)

/-- For an odd prime, the polar derivative of the displayed quadratic F is a
    linear injection off zero and its exact image is the displayed plane W_u. -/
def claim27883 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (_hodd : Odd p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ u : Plane p, u ≠ 0 →
      isLinearPolarDerivative p u ∧
      Function.Injective (polarDerivative p u) ∧
      Set.range (polarDerivative p u) =
        (displacementPlane p u : Set (Target p))

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27883
