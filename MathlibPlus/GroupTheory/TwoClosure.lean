import Mathlib

namespace MathlibPlus.GroupTheory.TwoClosure

variable {α : Type*} [Fintype α]

/-- The orbit of `x` under the point stabilizer of `o` in `G`. -/
def pointStabilizerOrbit (G : Subgroup (Equiv.Perm α)) (o x : α) : Set α :=
  {y | ∃ g : Equiv.Perm α, g ∈ G ∧ g o = o ∧ g x = y}

/-- Membership in the 2-closure, expressed as preservation of each ordered-pair
orbit. -/
def inTwoClosure (G : Subgroup (Equiv.Perm α)) (q : Equiv.Perm α) : Prop :=
  ∀ x y : α, ∃ g : Equiv.Perm α,
    g ∈ G ∧ g x = q x ∧ g y = q y

private lemma partial_map_eq (G : Subgroup (Equiv.Perm α))
    (q : Equiv.Perm α) (o x : α) (hq : inTwoClosure G q) (hqo : q o = o) :
    q '' pointStabilizerOrbit G o x ⊆ pointStabilizerOrbit G o x := by
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨k, hk, hko, hkx⟩ := hz
  obtain ⟨g, hg, hgo, hgz⟩ := hq o z
  refine ⟨g * k, G.mul_mem hg hk, ?_, ?_⟩
  · change g (k o) = o
    rw [hko]
    simpa [hqo] using hgo
  · change g (k x) = q z
    rw [hkx]
    exact hgz

/-- If a permutation belongs to the 2-closure and fixes `o`, it preserves
setwise every orbit of the point stabilizer of `o`. -/
theorem map_pointStabilizerOrbit_eq (G : Subgroup (Equiv.Perm α))
    (q : Equiv.Perm α) (o : α) (hq : inTwoClosure G q) (hqo : q o = o) :
    ∀ x : α, q '' pointStabilizerOrbit G o x = pointStabilizerOrbit G o x := by
  intro x
  apply Set.eq_of_subset_of_ncard_le (partial_map_eq G q o x hq hqo) _ (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ q.injective]

/-- A point-stabilizer orbit moved setwise by `q` certifies that `q` is outside
this 2-closure. -/
theorem not_inTwoClosure_of_orbit_moved
    (G : Subgroup (Equiv.Perm α)) (q : Equiv.Perm α) (o : α)
    (hqo : q o = o)
    (hmoved : ∃ x : α,
      q '' pointStabilizerOrbit G o x ≠ pointStabilizerOrbit G o x) :
    ¬ inTwoClosure G q := by
  intro hq
  obtain ⟨x, hx⟩ := hmoved
  exact hx (map_pointStabilizerOrbit_eq G q o hq hqo x)

/-- Two-closure is monotone under subgroup inclusion. -/
theorem inTwoClosure_mono_claim38366
    (H A : Subgroup (Equiv.Perm α)) (hHA : H ≤ A)
    (q : Equiv.Perm α) :
    inTwoClosure H q → inTwoClosure A q := by
  intro hq x y
  obtain ⟨g, hg, hx, hy⟩ := hq x y
  exact ⟨g, hHA hg, hx, hy⟩

end MathlibPlus.GroupTheory.TwoClosure
