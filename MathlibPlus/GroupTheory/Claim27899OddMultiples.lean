import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.Claim27899

/--
Claim 27899: in a finite abelian group of odd order, multiplication of an
element by `-2` does not change the cyclic additive subgroup it generates.
The odd-order hypothesis is stated with `Nat.card`, the canonical finite
cardinality, rather than a chosen enumeration.
-/
theorem oddOrderCyclicSubgroup_mulNegTwo
    {A : Type*} [AddCommGroup A] [Finite A]
    (hcard : Odd (Nat.card A)) (c : A) :
    AddSubgroup.zmultiples ((-2 : ℤ) • c) = AddSubgroup.zmultiples c := by
  have hn_dvd : addOrderOf c ∣ Nat.card A := addOrderOf_dvd_natCard c
  have hn_odd : Odd (addOrderOf c) := by
    apply Nat.not_even_iff_odd.mp
    intro heven
    obtain ⟨d, hd⟩ := hn_dvd
    obtain ⟨r, hr⟩ := heven
    have heven_card : Even (Nat.card A) := by
      refine ⟨r * d, ?_⟩
      rw [hd, hr]
      ring
    exact (Nat.not_even_iff_odd.mpr hcard) heven_card
  apply le_antisymm
  · apply (AddSubgroup.zmultiples_le).2
    exact AddSubgroup.zsmul_mem_zmultiples c (-2)
  · apply (AddSubgroup.zmultiples_le).2
    obtain ⟨q, hq⟩ := hn_odd
    change ∃ k : ℤ, k • ((-2 : ℤ) • c) = c
    refine ⟨-((q + 1 : ℕ) : ℤ), ?_⟩
    have hnzero : (addOrderOf c : ℤ) • c = 0 := by
      exact_mod_cast addOrderOf_nsmul_eq_zero c
    rw [smul_smul]
    have hscalar :
        (-((q + 1 : ℕ) : ℤ)) * (-2 : ℤ) = (addOrderOf c : ℤ) + 1 := by
      rw [hq]
      push_cast
      ring
    rw [hscalar, add_zsmul, hnzero]
    simp

end MathlibPlus.GroupTheory.Claim27899
