import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim37378

/-!
The claim's ordered-orbital content is formalized directly with ranges of the
subgroup actions, so no new orbital definition is introduced.  The unordered
quotient convention is not specified in the source text; the corresponding
ordered-pair statement is therefore the precise interface used here.
-/

/-- A subgroup orbit of a point is contained in the orbit for the larger
subgroup. -/
theorem point_orbit_subset
    {Ω : Type*} (K E : Subgroup (Equiv.Perm Ω)) (hKE : K ≤ E) (x : Ω) :
    Set.range (fun k : K => (k : Equiv.Perm Ω) x) ⊆
      Set.range (fun e : E => (e : Equiv.Perm Ω) x) := by
  rintro y ⟨k, rfl⟩
  exact ⟨⟨k, hKE k.property⟩, rfl⟩

/-- The same inclusion holds for ordered pairs under the diagonal action. -/
theorem ordered_pair_orbit_subset
    {Ω : Type*} (K E : Subgroup (Equiv.Perm Ω)) (hKE : K ≤ E)
    (x y : Ω) :
    Set.range (fun k : K =>
      ((k : Equiv.Perm Ω) x, (k : Equiv.Perm Ω) y)) ⊆
      Set.range (fun e : E =>
        ((e : Equiv.Perm Ω) x, (e : Equiv.Perm Ω) y)) := by
  rintro z ⟨k, rfl⟩
  exact ⟨⟨k, hKE k.property⟩, rfl⟩

/-- Every ordered `E`-orbit is the union of the `K`-orbits of its points. -/
theorem ordered_pair_orbit_is_union
    {Ω : Type*} (K E : Subgroup (Equiv.Perm Ω)) (hKE : K ≤ E)
    (x y : Ω) :
    Set.range (fun e : E =>
        ((e : Equiv.Perm Ω) x, (e : Equiv.Perm Ω) y)) =
      ⋃ z : Set.range (fun e : E =>
          ((e : Equiv.Perm Ω) x, (e : Equiv.Perm Ω) y)),
        Set.range (fun k : K =>
          ((k : Equiv.Perm Ω) z.1.1, (k : Equiv.Perm Ω) z.1.2)) := by
  ext z
  constructor
  · rintro ⟨e, rfl⟩
    refine Set.mem_iUnion.2 ⟨
      ⟨((e : Equiv.Perm Ω) x, (e : Equiv.Perm Ω) y), ⟨e, rfl⟩⟩, ?_⟩
    exact ⟨1, by simp⟩
  · intro hz
    rcases Set.mem_iUnion.1 hz with ⟨u, hu⟩
    rcases hu with ⟨k, hk⟩
    rcases u.2 with ⟨e, he⟩
    refine ⟨⟨k * e, ?_⟩, ?_⟩
    · exact E.mul_mem (hKE k.property) e.property
    · rw [← he] at hk
      simpa [mul_apply] using hk

/-- A permutation preserving each member of a family setwise preserves their
union.  This is the set-theoretic step used after the orbital decomposition. -/
theorem image_iUnion_of_setwise_preservation
    {α ι : Type*} (f : Equiv.Perm α) (s : ι → Set α)
    (h : ∀ i, f '' s i = s i) :
    f '' (⋃ i, s i) = ⋃ i, s i := by
  rw [Set.image_iUnion]
  simp_rw [h]

end MathlibPlus.GroupTheory.Claim37378
