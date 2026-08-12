import Mathlib

namespace MathlibPlus.Algebra.TranslationPeriod

noncomputable section

variable {B : Type*} [AddCommGroup B]

/-- The translate of a set by an element of its ambient additive group. -/
def translateSet (S : Set B) (u : B) : Set B := (fun x => x + u) '' S

private theorem translateSet_add (S : Set B) (a b : B) :
    translateSet S (a + b) = translateSet (translateSet S a) b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + a, ⟨x, hx, rfl⟩, ?_⟩
    simp [translateSet, add_assoc]
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [translateSet, add_assoc]

/-- The full translation period subgroup of a set. -/
def periodSubgroup (X : Set B) : AddSubgroup B :=
  { carrier := {u | translateSet X u = X}
    zero_mem' := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [translateSet] using hx
      · intro hy
        exact ⟨y, hy, by simp⟩
    add_mem' := by
      intro a b ha hb
      change translateSet X (a + b) = X
      rw [translateSet_add, ha, hb]
    neg_mem' := by
      intro a ha
      change translateSet X (-a) = X
      have h := translateSet_add X a (-a)
      rw [ha] at h
      simpa [translateSet] using h.symm }

/--
The full translation period is a subgroup, and quotienting by it produces an
aperiodic image.  The source claim did not specify finiteness or a coefficient
field, so this is stated for every additive commutative group and every set.
-/
theorem fullTranslationPeriodAperiodicQuotient (X : Set B) :
    let P := periodSubgroup X
    (∀ u : B, u ∈ P ↔ translateSet X u = X) ∧
      let q : B →+ (B ⧸ P) := QuotientAddGroup.mk' P
      let Y : Set (B ⧸ P) := q '' X
      ∀ y : B ⧸ P, translateSet Y y = Y → y = 0 := by
  dsimp
  constructor
  · intro u
    rfl
  · let q : B →+ (B ⧸ periodSubgroup X) := QuotientAddGroup.mk' (periodSubgroup X)
    let Y : Set (B ⧸ periodSubgroup X) := q '' X
    intro y hy
    change translateSet Y y = Y at hy
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (periodSubgroup X) y
    have hzperiod : translateSet X z = X := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hleft : q (x + z) ∈ translateSet Y (q z) := by
          refine ⟨q x, ⟨x, hx, rfl⟩, ?_⟩
          simp only [map_add]
        have hright : q (x + z) ∈ Y := by
          rw [← hy]
          exact hleft
        rcases hright with ⟨x', hx', hq⟩
        obtain ⟨p, hp, hxp⟩ :=
          (QuotientAddGroup.mk'_eq_mk' (periodSubgroup X)).mp hq
        have hpperiod : translateSet X p = X := hp
        have hmem : x' + p ∈ X := by
          rw [← hpperiod]
          exact ⟨x', hx', rfl⟩
        simpa [hxp] using hmem
      · intro hw
        have hleft : q w ∈ translateSet Y (q z) := by
          rw [hy]
          exact ⟨w, hw, rfl⟩
        rcases hleft with ⟨y', ⟨x', hx', rfl⟩, hq⟩
        have hq' : q (x' + z) = q w := by
          simpa only [map_add] using hq
        obtain ⟨p, hp, hxp⟩ :=
          (QuotientAddGroup.mk'_eq_mk' (periodSubgroup X)).mp hq'
        have hpperiod : translateSet X p = X := hp
        have hmem : x' + p ∈ X := by
          rw [← hpperiod]
          exact ⟨x', hx', rfl⟩
        refine ⟨x' + p, hmem, ?_⟩
        simpa [add_assoc, add_comm, add_left_comm] using hxp
    have hzmem : z ∈ periodSubgroup X := hzperiod
    have hzker : z ∈ q.ker := by
      rw [QuotientAddGroup.ker_mk']
      exact hzmem
    exact AddMonoidHom.mem_ker.mp hzker

/-- Claim 41936: every nonempty proper subset of `C₇` has trivial translation period. -/
theorem claim41936 (U : Set (ZMod 7)) (hne : U.Nonempty)
    (hproper : U ≠ Set.univ) :
    ∀ t : ZMod 7, translateSet U t = U → t = 0 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro t ht
  by_contra ht0
  let P := periodSubgroup U
  have htP : t ∈ P := ht
  have hPtop : P = ⊤ := by
    apply (AddSubgroup.eq_top_iff' P).2
    intro y
    obtain ⟨n, hn⟩ :=
      (AddSubgroup.mem_zmultiples_iff).mp
        (mem_zmultiples_of_prime_card (p := 7) (g := t) (g' := y)
          (Nat.card_zmod 7) ht0)
    exact hn ▸ P.zsmul_mem htP n
  have hperiod : ∀ y : ZMod 7, translateSet U y = U := by
    intro y
    have hy : y ∈ P := by
      rw [hPtop]
      exact AddSubgroup.mem_top y
    exact hy
  obtain ⟨x, hx⟩ := hne
  apply hproper
  apply Set.eq_univ_of_forall
  intro y
  have hmem : x + (y - x) ∈ U := by
    have htrans : x + (y - x) ∈ translateSet U (y - x) := by
      exact ⟨x, hx, rfl⟩
    rw [hperiod (y - x)] at htrans
    exact htrans
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hmem

end
end MathlibPlus.Algebra.TranslationPeriod
