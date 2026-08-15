import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

/-- The union of a basis and its negatives. -/
def signedBasisSet {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (a : Module.Basis ι K V) : Set V :=
  Set.range a ∪ Set.range (fun i => -(a i))

/-- A linear automorphism transports any signed basis to any other one. -/
def claim_59998 : Prop :=
  (∀ (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V]
      (a b : Module.Basis ι K V),
      ∃ e : V ≃ₗ[K] V,
        e '' signedBasisSet a = signedBasisSet b) ∧
    (∀ (p r : ℕ) (hp : Nat.Prime p),
      5 ≤ p → 6 ≤ r → r ≤ 2 * p + 2 →
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (a b : Module.Basis (Fin r) (ZMod p) (Fin r → ZMod p)),
          ∃ e : (Fin r → ZMod p) ≃ₗ[ZMod p] (Fin r → ZMod p),
            e '' signedBasisSet a = signedBasisSet b)

end
end MathlibPlus.Open.Research
