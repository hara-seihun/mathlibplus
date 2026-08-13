import Mathlib

open scoped Pointwise

namespace MathlibPlus.Algebra

/--
Claim 36996, in the additive-coset form of the displacement argument.
The hypothesis says that every displacement `q x - x` lies in `H`; the
source's `Wᵤ ≤ H` is the corresponding generated-displacement formulation.
-/
theorem displacementContainment_claim36996
    {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (q : G → G)
    (hdisp : ∀ x : G, q x - x ∈ H) :
    ∀ x : G,
      ({x} : Set G) + (H : Set G) =
        ({x + q 0} : Set G) + (H : Set G) := by
  intro x
  ext y
  rw [Set.mem_add, Set.mem_add]
  have hq0 : q 0 ∈ H := by
    simpa using hdisp 0
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Set.mem_singleton_iff] at ha
    subst a
    refine ⟨x + q 0, rfl, b - q 0, H.sub_mem hb hq0, ?_⟩
    calc
      (x + q 0) + (b - q 0) = x + b := by abel
      _ = y := hab
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Set.mem_singleton_iff] at ha
    subst a
    refine ⟨x, rfl, q 0 + b, H.add_mem hq0 hb, ?_⟩
    calc
      x + (q 0 + b) = (x + q 0) + b := by abel
      _ = y := hab

end MathlibPlus.Algebra
