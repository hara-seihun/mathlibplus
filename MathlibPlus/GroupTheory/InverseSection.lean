import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Set.Basic

namespace MathlibPlus.GroupTheory

/--
Claim 29776 (R-1034): inverse closure of a subset of a direct product is
exactly the inverse-pair condition on its fibre sections.
-/
theorem inverseClosed_iff_sectionPair {A H : Type*} [Group A] [Group H]
    (S : Set (A × H)) :
    (∀ x, x ∈ S ↔ x⁻¹ ∈ S) ↔
      ∀ h : H, ∀ a : A, ((a, h⁻¹) ∈ S ↔ (a⁻¹, h) ∈ S) := by
  constructor
  · intro hS h a
    constructor
    · intro ha
      simpa using (hS (a, h⁻¹)).mp ha
    · intro ha
      simpa using (hS (a⁻¹, h)).mp ha
  · intro hsection x
    rcases x with ⟨a, h⟩
    constructor
    · intro hx
      have hi : (a⁻¹, h⁻¹) ∈ S ↔ (a, h) ∈ S := by
        simpa using hsection h (a⁻¹)
      exact hi.mpr hx
    · intro hx
      have hi : (a⁻¹, h⁻¹) ∈ S ↔ (a, h) ∈ S := by
        simpa using hsection h (a⁻¹)
      exact hi.mp hx

end MathlibPlus.GroupTheory
