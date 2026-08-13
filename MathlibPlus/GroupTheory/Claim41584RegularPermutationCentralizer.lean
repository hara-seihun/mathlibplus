import Mathlib

namespace MathlibPlus.GroupTheory.Claim41584

/--
The regularity witness for a permutation copy is an equivalence `e : G ≃ Ω`
under which the displayed copy is the left regular representation.  The
centralizer is then exactly the transported right regular representation.
-/
theorem mem_centralizer_regularPermutationCopy_iff
    {G Ω : Type*} [Group G]
    (R : Subgroup (Equiv.Perm Ω)) (e : G ≃ Ω)
    (hR : (R : Set (Equiv.Perm Ω)) =
      Set.range (fun g : G => (e.symm.trans (Equiv.mulLeft g)).trans e))
    (p : Equiv.Perm Ω) :
    p ∈ Subgroup.centralizer (R : Set (Equiv.Perm Ω)) ↔
      ∃ a : G, p = (e.symm.trans (Equiv.mulRight a)).trans e := by
  rw [hR]
  constructor
  · intro hp
    have hc := Subgroup.mem_centralizer_iff.mp hp
    let a : G := e.symm (p (e 1))
    refine ⟨a, ?_⟩
    apply Equiv.Perm.ext
    intro x
    let g : G := e.symm x
    have h := hc ((e.symm.trans (Equiv.mulLeft g)).trans e) ⟨g, rfl⟩
    have h' := congrArg (fun q : Equiv.Perm Ω => q (e 1)) h
    simpa [Equiv.trans_apply, Equiv.Perm.mul_def, Equiv.mulLeft,
      Equiv.mulRight, a, g] using h'.symm
  · rintro ⟨a, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro h hh
    rcases hh with ⟨g, rfl⟩
    apply Equiv.Perm.ext
    intro x
    simp [Equiv.trans_apply, Equiv.Perm.mul_def, Equiv.mulLeft,
      Equiv.mulRight, mul_assoc]

/-- In the abelian case, the transported opposite regular copy is the
transported displayed copy itself. -/
theorem mem_centralizer_abelianRegularPermutationCopy_iff
    {G Ω : Type*} [CommGroup G]
    (R : Subgroup (Equiv.Perm Ω)) (e : G ≃ Ω)
    (hR : (R : Set (Equiv.Perm Ω)) =
      Set.range (fun g : G => (e.symm.trans (Equiv.mulLeft g)).trans e))
    (p : Equiv.Perm Ω) :
    p ∈ Subgroup.centralizer (R : Set (Equiv.Perm Ω)) ↔
      ∃ a : G, p = (e.symm.trans (Equiv.mulLeft a)).trans e := by
  rw [mem_centralizer_regularPermutationCopy_iff R e hR]
  constructor
  · rintro ⟨a, h⟩
    refine ⟨a, h.trans ?_⟩
    apply Equiv.Perm.ext
    intro x
    simp [Equiv.trans_apply, Equiv.mulLeft, Equiv.mulRight, mul_comm]
  · rintro ⟨a, h⟩
    refine ⟨a, h.trans ?_⟩
    apply Equiv.Perm.ext
    intro x
    simp [Equiv.trans_apply, Equiv.mulLeft, Equiv.mulRight, mul_comm]

/-- Equality form of the abelian regular-permutation centralizer claim. -/
theorem centralizer_abelianRegularPermutationCopy_eq
    {G Ω : Type*} [CommGroup G]
    (R : Subgroup (Equiv.Perm Ω)) (e : G ≃ Ω)
    (hR : (R : Set (Equiv.Perm Ω)) =
      Set.range (fun g : G => (e.symm.trans (Equiv.mulLeft g)).trans e)) :
    Subgroup.centralizer (R : Set (Equiv.Perm Ω)) = R := by
  ext p
  rw [mem_centralizer_abelianRegularPermutationCopy_iff R e hR]
  constructor
  · rintro ⟨a, rfl⟩
    change (e.symm.trans (Equiv.mulLeft a)).trans e ∈ (R : Set (Equiv.Perm Ω))
    rw [hR]
    exact ⟨a, rfl⟩
  · intro hp
    have hp' : p ∈ Set.range
        (fun g : G => (e.symm.trans (Equiv.mulLeft g)).trans e) := by
      change p ∈ (R : Set (Equiv.Perm Ω)) at hp
      rw [hR] at hp
      exact hp
    rcases hp' with ⟨a, rfl⟩
    exact ⟨a, rfl⟩

end MathlibPlus.GroupTheory.Claim41584
