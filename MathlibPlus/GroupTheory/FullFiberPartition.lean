import Mathlib

namespace MathlibPlus.GroupTheory.FullFiberPartition

/--
Independent full symmetric actions on every fibre determine that fibre
partition uniquely among partitions with the same block size.

This is the invariant-partition core used in wreath-product CI quotient
descent: no graph assumptions are needed once the independent fibre
permutations are known to act.
-/
theorem unique_equipartition_of_fullFiberSymmetry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty κ]
    (C : Set (Set (ι × κ)))
    (singleFiber : ι → Equiv.Perm κ → Equiv.Perm (ι × κ))
    (singleFiber_apply : ∀ (i : ι) (σ : Equiv.Perm κ) (x : ι × κ),
      singleFiber i σ x = if x.1 = i then (x.1, σ x.2) else x)
    (partition : ∀ x : ι × κ, ∃! c : Set (ι × κ), c ∈ C ∧ x ∈ c)
    (blockCard : ∀ c ∈ C, c.ncard = Fintype.card κ)
    (invariant : ∀ (i : ι) (σ : Equiv.Perm κ) (c : Set (ι × κ)),
      c ∈ C → singleFiber i σ '' c ∈ C) :
    C = Set.range (fun i : ι => {x : ι × κ | x.1 = i}) := by
  classical
  have block_eq_of_common_point
      {c d : Set (ι × κ)} (hc : c ∈ C) (hd : d ∈ C)
      {x : ι × κ} (hxc : x ∈ c) (hxd : x ∈ d) : c = d := by
    obtain ⟨b, hb, unique⟩ := partition x
    have hc_eq : c = b := unique c ⟨hc, hxc⟩
    have hd_eq : d = b := unique d ⟨hd, hxd⟩
    exact hc_eq.trans hd_eq.symm
  have fiberCard (i : ι) :
      {x : ι × κ | x.1 = i}.ncard = Fintype.card κ := by
    have fiber_eq : {x : ι × κ | x.1 = i} =
        Set.range (fun k : κ => (i, k)) := by
      ext x
      constructor
      · intro hx
        exact ⟨x.2, Prod.ext hx.symm rfl⟩
      · rintro ⟨k, rfl⟩
        rfl
    rw [fiber_eq]
    calc
      (Set.range (fun k : κ => (i, k))).ncard = Nat.card κ :=
        Set.ncard_range_of_injective (fun _ _ h => congrArg Prod.snd h)
      _ = Fintype.card κ := Nat.card_eq_fintype_card
  have C_subset :
      C ⊆ Set.range (fun i : ι => {x : ι × κ | x.1 = i}) := by
    intro c hc
    have cCardPos : 0 < c.ncard := by
      rw [blockCard c hc]
      exact Fintype.card_pos
    obtain ⟨x, hxc⟩ := (Set.ncard_pos (s := c)).mp cCardPos
    let i : ι := x.1
    let fiber : Set (ι × κ) := {y | y.1 = i}
    by_cases fiber_subset : fiber ⊆ c
    · have fiber_eq_c : fiber = c := by
        apply Set.eq_of_subset_of_ncard_le fiber_subset
        rw [blockCard c hc]
        exact (fiberCard i).ge
      exact ⟨i, fiber_eq_c⟩
    · obtain ⟨y, hyFiber, hyNotC⟩ := Set.not_subset.mp fiber_subset
      have c_subset_fiber : c ⊆ fiber := by
        intro z hzc
        by_contra hzFiber
        have hzFirst : z.1 ≠ i := by simpa [fiber] using hzFiber
        let σ : Equiv.Perm κ := Equiv.swap x.2 y.2
        let p : Equiv.Perm (ι × κ) := singleFiber i σ
        have hpX : p x = y := by
          rw [singleFiber_apply]
          simp only [i, σ, Equiv.swap_apply_left]
          exact Prod.ext hyFiber.symm rfl
        have hpZ : p z = z := by
          rw [singleFiber_apply]
          exact if_neg hzFirst
        have hpC : p '' c ∈ C := invariant i σ c hc
        have hyImage : y ∈ p '' c := ⟨x, hxc, hpX⟩
        have hzImage : z ∈ p '' c := ⟨z, hzc, hpZ⟩
        have c_eq_image : c = p '' c :=
          block_eq_of_common_point hc hpC hzc hzImage
        rw [← c_eq_image] at hyImage
        exact hyNotC hyImage
      have c_eq_fiber : c = fiber := by
        apply Set.eq_of_subset_of_ncard_le c_subset_fiber
        rw [blockCard c hc]
        exact (fiberCard i).le
      exact ⟨i, c_eq_fiber.symm⟩
  apply Set.Subset.antisymm C_subset
  rintro _ ⟨i, rfl⟩
  let k : κ := Classical.choice ‹Nonempty κ›
  obtain ⟨c, hc, _⟩ := partition (i, k)
  rcases C_subset hc.1 with ⟨j, rfl⟩
  have hij : i = j := by simpa using hc.2
  subst j
  exact hc.1

end MathlibPlus.GroupTheory.FullFiberPartition
