import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim29775

/-- The fibrewise map in the source construction. -/
def fiberMap {A H : Type*} (q : H → Equiv.Perm A) : A × H → A × H :=
  fun p => (q p.2 p.1, p.2)

/-- The active support of the family of fibre permutations. -/
def activeSupport {A H : Type*} [Group H] (q : H → Equiv.Perm A) : Set H :=
  {h | q h ≠ 1}

/-- For the active support of a family of fibre permutations, disjointness from
its inverse support is exactly the pointwise inverse-pair condition. -/
theorem inverse_pair_separated_iff
    {A H : Type*} [Fintype A] [Fintype H] [Group H]
    (q : H → Equiv.Perm A) :
    (activeSupport q ∩ {h | h⁻¹ ∈ activeSupport q} = (∅ : Set H)) ↔
      ∀ h, q h ≠ 1 → q h⁻¹ = 1 := by
  change ({h | q h ≠ 1} ∩ {h | h⁻¹ ∈ {h | q h ≠ 1}} = (∅ : Set H)) ↔ _
  constructor
  · intro hdis h hq
    by_contra hqinv
    have hx : h ∈ ({h : H | q h ≠ 1} ∩ {h : H | h⁻¹ ∈ {h : H | q h ≠ 1}}) := by
      exact ⟨hq, hqinv⟩
    have hx' : h ∈ ({h : H | q h ≠ 1} ∩ {h : H | q h⁻¹ ≠ 1}) := by
      simpa using hx
    have : h ∈ (∅ : Set H) := hdis ▸ hx'
    simpa using this
  · intro h
    ext x
    constructor
    · intro hx
      have hx' : q x ≠ 1 ∧ q x⁻¹ ≠ 1 := by
        simpa using hx
      exact False.elim (hx'.2 (h x hx'.1))
    · intro hx
      exact False.elim (by simpa using hx)

end MathlibPlus.GroupTheory.Claim29775
