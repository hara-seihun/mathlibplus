import Mathlib
import Mathlib.GroupTheory.SpecificGroups.Quaternion

namespace MathlibPlus.GroupTheory.Claim29039

/-- The odd- and 2-primary factors of `C₃² × Q₈` are intrinsically recovered
by the exponent-three and exponent-four equations, hence are characteristic. -/
theorem characteristicDirectFactors_orderCharacterization_claim29039 :
    let G := (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) × QuaternionGroup 2
    (∀ g : G, g ^ 3 = 1 ↔ g.2 = 1) ∧
      (∀ g : G, g ^ 4 = 1 ↔ g.1 = 1) ∧
      (∀ φ : G ≃* G, ∀ g : G,
        (g.2 = 1 ↔ (φ g).2 = 1) ∧
        (g.1 = 1 ↔ (φ g).1 = 1)) := by
  dsimp
  have h :
      (∀ g : (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) × QuaternionGroup 2,
        g ^ 3 = 1 ↔ g.2 = 1) ∧
      (∀ g : (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) × QuaternionGroup 2,
        g ^ 4 = 1 ↔ g.1 = 1) := by
    native_decide
  rcases h with ⟨h3, h4⟩
  refine ⟨h3, h4, ?_⟩
  intro φ g
  constructor
  · constructor
    · intro hg
      apply (h3 (φ g)).mp
      simpa [map_pow] using congrArg φ ((h3 g).mpr hg)
    · intro hg
      apply (h3 g).mp
      apply φ.injective
      simpa [map_pow] using (h3 (φ g)).mpr hg
  · constructor
    · intro hg
      apply (h4 (φ g)).mp
      simpa [map_pow] using congrArg φ ((h4 g).mpr hg)
    · intro hg
      apply (h4 g).mp
      apply φ.injective
      simpa [map_pow] using (h4 (φ g)).mpr hg

end MathlibPlus.GroupTheory.Claim29039
