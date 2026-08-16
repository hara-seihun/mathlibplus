import Mathlib

namespace MathlibPlus.Open.CayleyCI

noncomputable section
open Classical

def ConnectionSet {p d m : ℕ} (U : Fin m → Submodule (ZMod p) (Fin (2 * d) → ZMod p)) : Set (Fin (2 * d) → ZMod p) :=
  ⋃ i : Fin m, (U i : Set (Fin (2 * d) → ZMod p)) \ {0}

def IdentityFreeInverseClosed {V : Type*} [AddGroup V]
    (S : Set V) : Prop :=
  0 ∉ S ∧ ∀ x ∈ S, -x ∈ S

def CayleyGraphIsomorphism {V : Type*} [AddGroup V]
    (S T : Set V) (q : V ≃ V) : Prop :=
  ∀ x y, (x - y ∈ S ↔ q x - q y ∈ T)

def ProjectiveNetAffineThreshold : Prop :=
  ∀ (p d m : ℕ) [Fact (Nat.Prime p)],
    1 ≤ d → 3 ≤ m →
    let V := Fin (2 * d) → ZMod p
    ∀ (U W : Fin m → Submodule (ZMod p) V),
      (∀ i, Module.finrank (ZMod p) (U i) = d) ∧
      (∀ i, Module.finrank (ZMod p) (W i) = d) ∧
      (∀ i j, i ≠ j → IsCompl (U i) (U j)) ∧
      (∀ i j, i ≠ j → IsCompl (W i) (W j)) ∧
      p ^ d > 1 + m * (m - 2) →
      let S_U : Set V := ConnectionSet U
      let S_W : Set V := ConnectionSet W
      IdentityFreeInverseClosed S_U ∧
      IdentityFreeInverseClosed S_W ∧
      ∀ q : V ≃ V, CayleyGraphIsomorphism S_U S_W q →
        ∃ q₀ : V, ∃ α : V ≃ₗ[ZMod p] V, ∃ π : Fin m ≃ Fin m,
          (∀ v, q v = q₀ + α v) ∧
          (∀ i, Submodule.map α.toLinearMap (U i) = W (π i))

end
end MathlibPlus.Open.CayleyCI
