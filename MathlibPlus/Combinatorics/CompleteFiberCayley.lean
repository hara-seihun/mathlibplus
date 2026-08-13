import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace MathlibPlus.Combinatorics

/-- The associated Cayley graph has edges exactly within one first-coordinate
fiber, and distinct second coordinates are adjacent. -/
theorem completeFiberCayley_adj_claim35735
    {A H : Type*} [Group A] [Group H] [DecidableEq A] [DecidableEq H]
    (x y : A × H) :
    (SimpleGraph.mulCayley {g : A × H | g.1 = 1 ∧ g.2 ≠ 1}).Adj x y ↔
      x.1 = y.1 ∧ x.2 ≠ y.2 := by
  rw [SimpleGraph.mulCayley_adj]
  simp [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
    inv_mul_eq_one]
  constructor
  · rintro ⟨hxy, (⟨h, hk⟩ | ⟨h, hk⟩)⟩
    · exact ⟨h, hk⟩
    · refine ⟨h.symm, ?_⟩
      intro hxy₂
      exact hk hxy₂.symm
  · rintro ⟨h, hk⟩
    refine ⟨?_, Or.inl ⟨h, hk⟩⟩
    intro hxy
    apply hk
    exact congrArg Prod.snd hxy

/-- The edge relation of the same graph generates exactly the first-coordinate
fibers as connected components. -/
theorem completeFiberCayley_reachable_iff_claim35735
    {A H : Type*} [Group A] [Group H] [DecidableEq A] [DecidableEq H]
    (x y : A × H) :
    Relation.EqvGen
      (SimpleGraph.mulCayley {g : A × H | g.1 = 1 ∧ g.2 ≠ 1}).Adj x y ↔
      x.1 = y.1 := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
        exact (completeFiberCayley_adj_claim35735 x y).mp hxy |>.1
    | refl x => rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  · intro h
    by_cases hxy : x = y
    · subst y
      exact Relation.EqvGen.refl x
    · exact Relation.EqvGen.rel x y
        ((completeFiberCayley_adj_claim35735 x y).mpr ⟨h, by
          intro hsecond
          apply hxy
          apply Prod.ext h
          exact hsecond⟩)

/-- Each connected component fiber has the cardinality of the second factor. -/
theorem completeFiberCayley_fiber_card_claim35735
    {A H : Type*} [Group A] [Group H] [Fintype A] [Fintype H]
    [DecidableEq A] [DecidableEq H] (a : A) :
    Fintype.card {x : A × H // x.1 = a} = Fintype.card H := by
  let e : {x : A × H // x.1 = a} ≃ H :=
    { toFun := fun x => x.1.2
      invFun := fun h => ⟨(a, h), rfl⟩
      left_inv := by
        rintro ⟨⟨x₁, x₂⟩, hx⟩
        apply Subtype.ext
        simp [hx.symm]
      right_inv := by
        intro h
        rfl }
  exact Fintype.card_congr e

end MathlibPlus.Combinatorics
