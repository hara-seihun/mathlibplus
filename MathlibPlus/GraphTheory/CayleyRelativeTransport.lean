import Mathlib

namespace MathlibPlus.GraphTheory.CayleyRelativeTransport

/-- The directed right-Cayley relation with connection set `S`. -/
def rightCayleyRel {G : Type*} [Group G] (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

/-- The normalized relative transport permutation
`q_{f,x}(s) = f⁻¹ (f(x)⁻¹ f(xs))`. -/
def relativeTransport {G : Type*} [Group G] (f : Equiv.Perm G) (x : G) : Equiv.Perm G :=
  (Equiv.mulLeft x).trans
    (f.trans ((Equiv.mulLeft (f x)⁻¹).trans f.symm))

@[simp]
theorem relativeTransport_apply {G : Type*} [Group G]
    (f : Equiv.Perm G) (x s : G) :
    relativeTransport f x s = f.symm ((f x)⁻¹ * f (x * s)) := rfl

@[simp]
theorem relativeTransport_one {G : Type*} [Group G]
    (f : Equiv.Perm G) (hf : f 1 = 1) (x : G) :
    relativeTransport f x 1 = 1 := by
  rw [relativeTransport_apply, mul_one, inv_mul_cancel]
  calc
    f.symm 1 = f.symm (f 1) := congrArg f.symm hf.symm
    _ = 1 := f.symm_apply_apply 1

/-- Exact normalized relative-transport criterion for directed right-Cayley
relations. A pointed relabelling carries the relation with connection set `S`
to the relation with connection set `f '' S` exactly when every relative
transport permutation preserves `S` setwise. -/
theorem rightCayleyRel_transport_iff {G : Type*} [Group G] [Finite G]
    (f : Equiv.Perm G) (_hf : f 1 = 1) (S : Set G) :
    (∀ x y, rightCayleyRel S x y ↔ rightCayleyRel (f '' S) (f x) (f y)) ↔
      ∀ x, relativeTransport f x '' S = S := by
  constructor
  · intro h x
    have hmem : ∀ s, s ∈ S ↔ relativeTransport f x s ∈ S := by
      intro s
      have hs := h x (x * s)
      simpa [rightCayleyRel, relativeTransport] using hs
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hmem s).mp hs
    · intro ht
      refine ⟨(relativeTransport f x).symm t, ?_, by simp⟩
      exact (hmem _).mpr (by simpa using ht)
  · intro h x y
    have hmem : ∀ s, s ∈ S ↔ relativeTransport f x s ∈ S := by
      intro s
      constructor
      · intro hs
        rw [← h x]
        exact ⟨s, hs, rfl⟩
      · intro hqs
        rw [← h x] at hqs
        rcases hqs with ⟨t, ht, hts⟩
        have : t = s := (relativeTransport f x).injective hts
        simpa [this] using ht
    simpa [rightCayleyRel, relativeTransport] using hmem (x⁻¹ * y)

end MathlibPlus.GraphTheory.CayleyRelativeTransport
