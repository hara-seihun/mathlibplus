import Mathlib

namespace MathlibPlus.GroupTheory.Claim37155

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- A central element sends a point to another point fixed by the original
point stabilizer. -/
theorem central_stabilizer_fixes_central_translate (ω : Ω) (D : Subgroup G)
    (hD : D ≤ Subgroup.center G) {d : G} (hd : d ∈ D)
    {g : G} (hg : g ∈ MulAction.stabilizer G ω) :
    g • (d • ω) = d • ω := by
  rw [← mul_smul, (Subgroup.mem_center_iff.mp (hD hd) g), mul_smul]
  rw [MulAction.mem_stabilizer_iff.mp hg]

/-- The orbit of a point under a central subgroup is pointwise fixed by its
original point stabilizer, so each such point has a singleton stabilizer orbit. -/
theorem central_orbit_is_singleton_suborbit (ω : Ω) (D : Subgroup G)
    (hD : D ≤ Subgroup.center G) :
    ∀ z ∈ MulAction.orbit D ω,
      MulAction.orbit (MulAction.stabilizer G ω) z = {z} := by
  intro z hz
  rcases hz with ⟨d, rfl⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · simpa using (MulAction.mem_orbit z (1 : MulAction.stabilizer G ω))
  · intro y hy
    rcases hy with ⟨g, rfl⟩
    exact central_stabilizer_fixes_central_translate ω D hD
      (d := d.1) (g := g.1) d.property g.2

/-- Claim 37155, modeled as a finite faithful left action (the source uses
right permutation-action notation). -/
theorem claim37155
    {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype G] [Fintype Ω]
    [FaithfulSMul G Ω] (ω : Ω) (D : Subgroup G)
    (hD : D ≤ Subgroup.center G) :
    (∀ d ∈ D, ∀ g ∈ MulAction.stabilizer G ω, g • (d • ω) = d • ω) ∧
      (∀ z ∈ MulAction.orbit D ω,
        MulAction.orbit (MulAction.stabilizer G ω) z = {z}) := by
  constructor
  · intro d hd g hg
    exact central_stabilizer_fixes_central_translate ω D hD hd hg
  · exact central_orbit_is_singleton_suborbit ω D hD

end MathlibPlus.GroupTheory.Claim37155
