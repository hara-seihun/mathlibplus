import Batteries
import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.GroupTheory.TwoClosure

variable {α : Type*}

/-- Every element of the acting permutation group belongs to its binary
 two-closure. -/
theorem inTwoClosure_of_mem (G : Subgroup (Equiv.Perm α))
    {g : Equiv.Perm α} (hg : g ∈ G) : inTwoClosure G g := by
  intro x y
  exact ⟨g, hg, rfl, rfl⟩

/-- Saturation is transitive: taking the binary two-closure of a group all of
 whose elements already lie in the two-closure of `G` produces no permutation
 outside the two-closure of `G`. -/
theorem inTwoClosure_trans
    (G H : Subgroup (Equiv.Perm α))
    (hHG : ∀ h : Equiv.Perm α, h ∈ H → inTwoClosure G h)
    {q : Equiv.Perm α} (hq : inTwoClosure H q) :
    inTwoClosure G q := by
  intro x y
  obtain ⟨h, hh, hhx, hhy⟩ := hq x y
  obtain ⟨g, hg, hgx, hgy⟩ := hHG h hh x y
  exact ⟨g, hg, hgx.trans hhx, hgy.trans hhy⟩

/-- Any subgroup whose membership predicate is exactly binary two-closure
 membership realizes an idempotent closure: closing it again gives precisely
 the same permutations as closing the original group. -/
theorem inTwoClosure_idempotent_of_mem_iff
    (G H : Subgroup (Equiv.Perm α))
    (hH : ∀ q : Equiv.Perm α, q ∈ H ↔ inTwoClosure G q)
    (q : Equiv.Perm α) :
    inTwoClosure H q ↔ inTwoClosure G q := by
  constructor
  · exact inTwoClosure_trans G H (fun h hh => (hH h).mp hh)
  · intro hq
    intro x y
    obtain ⟨g, hg, hgx, hgy⟩ := hq x y
    exact ⟨g, (hH g).mpr (inTwoClosure_of_mem G hg), hgx, hgy⟩

end MathlibPlus.GroupTheory.TwoClosure
