import Batteries
import Mathlib

namespace MathlibPlus.GraphTheory

universe u

/-- If every identity-fixing permutation of a finite group is multiplicative,
then every finite fixed-label tuple of directed right-Cayley relations is CI.
The relation labels are fixed pointwise, not merely permuted. -/
theorem binaryRelationalCI_of_pointedEquiv_multiplicative
    {G : Type u} [Group G] [Finite G]
    (hpointed : ∀ e : G ≃ G, e 1 = 1 → ∀ x y : G, e (x * y) = e x * e y) :
    ∀ (κ : Type) [Finite κ] (S T : κ → Set G) (f : G ≃ G),
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (f x)⁻¹ * f y ∈ T i) →
        ∃ φ : G ≃* G, ∀ i, φ '' S i = T i := by
  intro κ _ S T f hf
  let e : G ≃ G := f.trans (Equiv.mulLeft (f 1)⁻¹)
  have he_one : e 1 = 1 := by
    simp [e]
  let φ : G ≃* G :=
    { e with map_mul' := hpointed e he_one }
  refine ⟨φ, ?_⟩
  intro i
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hrel := (hf i 1 s).mp (by simpa using hs)
    change (f 1)⁻¹ * f s ∈ T i at hrel
    simpa [φ, e] using hrel
  · intro ht
    let s : G := φ.symm t
    have htarget : (f 1)⁻¹ * f s ∈ T i := by
      simpa [s, φ, e] using ht
    have hsource := (hf i 1 s).mpr htarget
    refine ⟨s, by simpa using hsource, ?_⟩
    exact φ.apply_symm_apply t

/-- The cyclic group of order two is binary-relational CI: every finite tuple
of directed Cayley relations has the CI property simultaneously. -/
theorem cyclicTwo_binaryRelationalCI :
    ∀ (κ : Type) [Finite κ]
      (S T : κ → Set (Multiplicative (ZMod 2)))
      (f : Multiplicative (ZMod 2) ≃ Multiplicative (ZMod 2)),
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (f x)⁻¹ * f y ∈ T i) →
        ∃ φ : Multiplicative (ZMod 2) ≃* Multiplicative (ZMod 2),
          ∀ i, φ '' S i = T i := by
  apply binaryRelationalCI_of_pointedEquiv_multiplicative
  native_decide

/-- The cyclic group of order three is binary-relational CI: every finite tuple
of directed Cayley relations has the CI property simultaneously. -/
theorem cyclicThree_binaryRelationalCI :
    ∀ (κ : Type) [Finite κ]
      (S T : κ → Set (Multiplicative (ZMod 3)))
      (f : Multiplicative (ZMod 3) ≃ Multiplicative (ZMod 3)),
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (f x)⁻¹ * f y ∈ T i) →
        ∃ φ : Multiplicative (ZMod 3) ≃* Multiplicative (ZMod 3),
          ∀ i, φ '' S i = T i := by
  apply binaryRelationalCI_of_pointedEquiv_multiplicative
  native_decide

end MathlibPlus.GraphTheory
