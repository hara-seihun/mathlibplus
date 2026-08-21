-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Batteries
import Mathlib

namespace MathlibPlus.GraphTheory

@[instance_reducible] private def cyclicFourDecidableForallEquiv
    (A B : Finset (Multiplicative (ZMod 4))) :
    Decidable (∀ e : Multiplicative (ZMod 4) ≃ Multiplicative (ZMod 4),
      (∀ x y : Multiplicative (ZMod 4),
        x⁻¹ * y ∈ A ↔ (e x)⁻¹ * e y ∈ B) →
      (∀ g : Multiplicative (ZMod 4), g ∈ A ↔ g ∈ B) ∨
        (∀ g : Multiplicative (ZMod 4), g ∈ A ↔ g⁻¹ ∈ B)) :=
  inferInstance

attribute [local instance] cyclicFourDecidableForallEquiv

/-- The cyclic group of order four is a DCI-group in the direct connection-set
form: every isomorphism between directed right-Cayley relations has either the
identity or inversion automorphism as a connection-set shadow. Loops are
allowed; no inverse-closure hypothesis is imposed. -/
theorem cyclicFour_directedCayleyCI :
    ∀ (S T : Set (Multiplicative (ZMod 4)))
      (f : Multiplicative (ZMod 4) ≃ Multiplicative (ZMod 4)),
      (∀ x y, x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T) →
        ∃ φ : Multiplicative (ZMod 4) ≃* Multiplicative (ZMod 4),
          φ '' S = T := by
  intro S T f hf
  let SF : Finset (Multiplicative (ZMod 4)) := S.toFinite.toFinset
  let TF : Finset (Multiplicative (ZMod 4)) := T.toFinite.toFinset
  have hfinite :
      ∀ (A B : Finset (Multiplicative (ZMod 4)))
        (e : Multiplicative (ZMod 4) ≃ Multiplicative (ZMod 4)),
        (∀ x y : Multiplicative (ZMod 4),
          x⁻¹ * y ∈ A ↔ (e x)⁻¹ * e y ∈ B) →
        (∀ g : Multiplicative (ZMod 4), g ∈ A ↔ g ∈ B) ∨
          (∀ g : Multiplicative (ZMod 4), g ∈ A ↔ g⁻¹ ∈ B) := by
    native_decide
  have hrel : ∀ x y : Multiplicative (ZMod 4),
      x⁻¹ * y ∈ SF ↔ (f x)⁻¹ * f y ∈ TF := by
    intro x y
    simpa [SF, TF] using hf x y
  rcases hfinite SF TF f hrel with hid | hinv
  · refine ⟨MulEquiv.refl _, ?_⟩
    ext g
    simpa [SF, TF] using hid g
  · let ι : Multiplicative (ZMod 4) ≃* Multiplicative (ZMod 4) :=
      { toFun := fun x => x⁻¹
        invFun := fun x => x⁻¹
        left_inv := inv_inv
        right_inv := inv_inv
        map_mul' := by
          intro x y
          simp [mul_comm] }
    refine ⟨ι, ?_⟩
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      have := (hinv s).mp (by simpa [SF] using hs)
      simpa [TF, ι] using this
    · intro hg
      let s : Multiplicative (ZMod 4) := g⁻¹
      have hs : s ∈ S := by
        have : s⁻¹ ∈ TF := by simpa [s, TF] using hg
        have : s ∈ SF := (hinv s).mpr this
        simpa [s, SF] using this
      refine ⟨s, hs, ?_⟩
      simp [s, ι]

end MathlibPlus.GraphTheory
