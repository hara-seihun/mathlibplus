import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27884

private abbrev Plane (p : ℕ) := ZMod p × ZMod p

private def derivative (p : ℕ) (φ : Plane p → ZMod p)
    (u c : Plane p) : ZMod p :=
  φ (u + c) - φ u - φ c

private def quietAt (p : ℕ) (φ : Plane p → ZMod p)
    (u : Plane p) : Prop :=
  (∀ c d : Plane p,
    derivative p φ u (c + d) =
      derivative p φ u c + derivative p φ u d) ∧
    (∀ a : ZMod p, ∀ c : Plane p,
      derivative p φ u (a • c) = a • derivative p φ u c)

private def quietLocus (p : ℕ) (φ : Plane p → ZMod p) : Set (Plane p) :=
  {u | quietAt p φ u}

private def bilinearDerivative (p : ℕ) (φ : Plane p → ZMod p)
    (u c : Plane p) : ZMod p :=
  derivative p φ u c

/-- For a normalized plane-fiber function over an odd prime field, the quiet
    locus is a vector subspace and its polar derivative is bilinear there. -/
def claim27884 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (_hodd : Odd p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (φ : Plane p → ZMod p), φ 0 = 0 →
      (0 ∈ quietLocus p φ ∧
        (∀ u v, u ∈ quietLocus p φ → v ∈ quietLocus p φ →
          u + v ∈ quietLocus p φ) ∧
        (∀ (a : ZMod p) (u : Plane p), u ∈ quietLocus p φ →
          a • u ∈ quietLocus p φ)) ∧
      (∀ (u v : Plane p), u ∈ quietLocus p φ → v ∈ quietLocus p φ →
        ∀ c,
          bilinearDerivative p φ (u + v) c =
            bilinearDerivative p φ u c + bilinearDerivative p φ v c) ∧
      (∀ (a : ZMod p) (u : Plane p), u ∈ quietLocus p φ → ∀ c,
        bilinearDerivative p φ (a • u) c =
          a • bilinearDerivative p φ u c) ∧
      (∀ (u : Plane p), u ∈ quietLocus p φ → ∀ c d,
        bilinearDerivative p φ u (c + d) =
          bilinearDerivative p φ u c + bilinearDerivative p φ u d) ∧
      (∀ (u : Plane p), u ∈ quietLocus p φ →
        ∀ (a : ZMod p) (c : Plane p),
        bilinearDerivative p φ u (a • c) =
          a • bilinearDerivative p φ u c)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27884
