import Batteries
import Mathlib

namespace MathlibPlus.GraphTheory.TwinPeriod

open scoped Pointwise

private theorem stabilizer_eq_bot_iff
    {G : Type*} [Group G] (U : Set G) :
    MulAction.stabilizer G U = ⊥ ↔
      ∀ x : G, x • U = U → x = 1 := by
  constructor
  · intro h x hx
    have hxmem : x ∈ MulAction.stabilizer G U := hx
    rw [h] at hxmem
    simpa using hxmem
  · intro h
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := h x hx
      simpa [hx1]
    · exact bot_le

private theorem raw_open_or_closed_dichotomy
    {G : Type*} [Group G] (S : Set G)
    (hSinv : S = S⁻¹) (hSone : 1 ∉ S) :
    (∀ x : G, x • S = S → x = 1) ∨
      (∀ x : G, x • insert 1 S = insert 1 S → x = 1) := by
  by_cases hopen : ∀ x : G, x • S = S → x = 1
  · exact Or.inl hopen
  · right
    push Not at hopen
    rcases hopen with ⟨x, hx, hx1⟩
    intro y hy
    by_contra hy1
    have hinv : ∀ {z : G}, z ∈ S → z⁻¹ ∈ S := by
      intro z hz
      rw [hSinv, Set.mem_inv]
      simpa using hz
    have hyS : y ∈ S := by
      have : y ∈ insert 1 S := by
        rw [← hy]
        exact ⟨1, Set.mem_insert 1 S, by simp⟩
      rcases this with (rfl | hyS)
      · exact (hy1 rfl).elim
      · exact hyS
    have hxS : x ∉ S := by
      intro hxmem
      have hxi : x⁻¹ ∈ S := hinv hxmem
      have : (1 : G) ∈ x • S := by
        exact ⟨x⁻¹, hxi, by simp⟩
      rw [hx] at this
      exact hSone this
    have hyx_not : y⁻¹ * x ∉ S := by
      intro hyx
      have himage : x ∈ y • insert 1 S :=
        ⟨y⁻¹ * x, Set.mem_insert_of_mem 1 hyx, by simp⟩
      rw [hy] at himage
      rcases himage with hxeq | hxmem
      · exact hx1 hxeq
      · exact hxS hxmem
    have hyx : y⁻¹ * x ∈ S := by
      have : y ∈ x • S := by rwa [hx]
      rcases this with ⟨z, hz, hxz⟩
      have hzi : z⁻¹ ∈ S := hinv hz
      have heq : y⁻¹ * x = z⁻¹ := by
        rw [← hxz]
        simp
      rwa [heq]
    exact hyx_not hyx

/-- Every loopless inverse-closed Cayley connection set is rigid in at least
one of its two canonical twin-period channels: either its open-neighborhood
left stabilizer is trivial, or the left stabilizer after adjoining the identity
(the closed-neighborhood channel) is trivial. -/
theorem open_or_closed_leftStabilizer_eq_bot
    {G : Type*} [Group G] (S : Set G)
    (hSinv : S = S⁻¹) (hSone : 1 ∉ S) :
    MulAction.stabilizer G S = ⊥ ∨
      MulAction.stabilizer G (insert 1 S) = ⊥ := by
  rw [stabilizer_eq_bot_iff, stabilizer_eq_bot_iff]
  exact raw_open_or_closed_dichotomy S hSinv hSone

private theorem mulCayley_neighborSet_eq_leftImage
    {G : Type*} [Group G] (S : Set G)
    (hSinv : S = S⁻¹) (hSone : 1 ∉ S) (x : G) :
    (SimpleGraph.mulCayley S).neighborSet x = x • S := by
  ext y
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact ⟨x⁻¹ * y, h, by simp⟩
    · refine ⟨x⁻¹ * y, ?_, by simp⟩
      have hi : (y⁻¹ * x)⁻¹ ∈ S := by
        rw [hSinv, Set.mem_inv]
        simpa using h
      simpa using hi
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, Or.inl (by simpa using hs)⟩
    intro hxs
    apply hSone
    have : s = 1 := by
      simpa using (congrArg (fun z => x⁻¹ * z) hxs).symm
    simpa [this] using hs

private theorem openRigid_of_normalizedIso
    {G : Type*} [Group G] {S T : Set G}
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T)
    (he1 : e 1 = 1)
    (hSrigid : ∀ x : G, x • S = S → x = 1) :
    ∀ y : G, y • T = T → y = 1 := by
  intro y hy
  let x := e.symm y
  have hyN : (SimpleGraph.mulCayley T).neighborSet y =
      (SimpleGraph.mulCayley T).neighborSet 1 := by
    rw [mulCayley_neighborSet_eq_leftImage T hTinv hTone,
      mulCayley_neighborSet_eq_leftImage T hTinv hTone]
    simpa using hy
  have hxN : (SimpleGraph.mulCayley S).neighborSet x =
      (SimpleGraph.mulCayley S).neighborSet 1 := by
    ext z
    change (SimpleGraph.mulCayley S).Adj x z ↔
      (SimpleGraph.mulCayley S).Adj 1 z
    rw [← e.map_rel_iff, ← e.map_rel_iff]
    have hex : e x = y := e.apply_symm_apply y
    rw [hex, he1]
    exact Set.ext_iff.mp hyN (e z)
  have hxP : x • S = S := by
    rw [mulCayley_neighborSet_eq_leftImage S hSinv hSone,
      mulCayley_neighborSet_eq_leftImage S hSinv hSone] at hxN
    simpa using hxN
  have hx1 := hSrigid x hxP
  calc
    y = e x := (e.apply_symm_apply y).symm
    _ = e 1 := by rw [hx1]
    _ = 1 := he1

private theorem closedRigid_of_normalizedIso
    {G : Type*} [Group G] {S T : Set G}
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T)
    (he1 : e 1 = 1)
    (hSrigid : ∀ x : G, x • insert 1 S = insert 1 S → x = 1) :
    ∀ y : G, y • insert 1 T = insert 1 T → y = 1 := by
  intro y hy
  let x := e.symm y
  have closed_eq (U : Set G) (hUinv : U = U⁻¹) (hUone : 1 ∉ U) (a : G) :
      insert a ((SimpleGraph.mulCayley U).neighborSet a) =
        a • insert 1 U := by
    rw [mulCayley_neighborSet_eq_leftImage U hUinv hUone]
    ext z
    constructor
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact ⟨1, Set.mem_insert 1 U, by simp⟩
      · exact ⟨u, Set.mem_insert_of_mem 1 hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rcases hu with rfl | hu
      · simp
      · exact Set.mem_insert_of_mem a ⟨u, hu, rfl⟩
  have hyC : insert y ((SimpleGraph.mulCayley T).neighborSet y) =
      insert 1 ((SimpleGraph.mulCayley T).neighborSet 1) := by
    rw [closed_eq T hTinv hTone, closed_eq T hTinv hTone]
    simpa using hy
  have hxC : insert x ((SimpleGraph.mulCayley S).neighborSet x) =
      insert 1 ((SimpleGraph.mulCayley S).neighborSet 1) := by
    ext z
    change (z = x ∨ (SimpleGraph.mulCayley S).Adj x z) ↔
      (z = 1 ∨ (SimpleGraph.mulCayley S).Adj 1 z)
    have heq : e z = y ↔ z = x := by
      constructor
      · intro h
        exact e.injective (h.trans (e.apply_symm_apply y).symm)
      · intro h
        rw [h]
        exact e.apply_symm_apply y
    have hone : e z = 1 ↔ z = 1 := by
      constructor
      · intro h
        apply e.injective
        simpa [he1] using h
      · rintro rfl
        exact he1
    rw [← heq, ← hone, ← e.map_rel_iff, ← e.map_rel_iff]
    have hex : e x = y := e.apply_symm_apply y
    rw [hex, he1]
    exact Set.ext_iff.mp hyC (e z)
  have hxP : x • insert 1 S = insert 1 S := by
    rw [closed_eq S hSinv hSone, closed_eq S hSinv hSone] at hxC
    simpa using hxC
  have hx1 := hSrigid x hxP
  calc
    y = e x := (e.apply_symm_apply y).symm
    _ = e 1 := by rw [hx1]
    _ = 1 := he1

/-- A normalized Cayley-graph isomorphism preserves triviality of the
open-neighborhood left-translation stabilizer exactly. -/
theorem open_leftStabilizer_eq_bot_iff_of_normalizedIso
    {G : Type*} [Group G] {S T : Set G}
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T)
    (he1 : e 1 = 1) :
    MulAction.stabilizer G S = ⊥ ↔
      MulAction.stabilizer G T = ⊥ := by
  rw [stabilizer_eq_bot_iff, stabilizer_eq_bot_iff]
  constructor
  · exact openRigid_of_normalizedIso hSinv hTinv hSone hTone e he1
  · have he1' : e.symm 1 = 1 := by
      apply e.injective
      simpa [he1]
    exact openRigid_of_normalizedIso hTinv hSinv hTone hSone e.symm he1'

/-- A normalized Cayley-graph isomorphism preserves triviality of the
closed-neighborhood left-translation stabilizer exactly. -/
theorem closed_leftStabilizer_eq_bot_iff_of_normalizedIso
    {G : Type*} [Group G] {S T : Set G}
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T)
    (he1 : e 1 = 1) :
    MulAction.stabilizer G (insert 1 S) = ⊥ ↔
      MulAction.stabilizer G (insert 1 T) = ⊥ := by
  rw [stabilizer_eq_bot_iff, stabilizer_eq_bot_iff]
  constructor
  · exact closedRigid_of_normalizedIso hSinv hTinv hSone hTone e he1
  · have he1' : e.symm 1 = 1 := by
      apply e.injective
      simpa [he1]
    exact closedRigid_of_normalizedIso hTinv hSinv hTone hSone e.symm he1'

/-- The common twin-period mechanism: for every normalized isomorphism of
loopless inverse-closed Cayley graphs, either both open-neighborhood period
subgroups are trivial, or both closed-neighborhood period subgroups are
trivial. -/
theorem normalizedIso_open_or_closed_stabilizers_eq_bot
    {G : Type*} [Group G] {S T : Set G}
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T)
    (he1 : e 1 = 1) :
    (MulAction.stabilizer G S = ⊥ ∧
      MulAction.stabilizer G T = ⊥) ∨
    (MulAction.stabilizer G (insert 1 S) = ⊥ ∧
      MulAction.stabilizer G (insert 1 T) = ⊥) := by
  rcases open_or_closed_leftStabilizer_eq_bot S hSinv hSone with hS | hS
  · exact Or.inl ⟨hS,
      (open_leftStabilizer_eq_bot_iff_of_normalizedIso
        hSinv hTinv hSone hTone e he1).mp hS⟩
  · exact Or.inr ⟨hS,
      (closed_leftStabilizer_eq_bot_iff_of_normalizedIso
        hSinv hTinv hSone hTone e he1).mp hS⟩

end MathlibPlus.GraphTheory.TwinPeriod
