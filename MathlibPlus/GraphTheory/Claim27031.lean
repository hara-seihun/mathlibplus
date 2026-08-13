import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace MathlibPlus.GraphTheory.Claim27031

open scoped Pointwise

private lemma mulCayley_neighborSet_ncard_eq
    {G : Type*} [Group G]
    (S : Set G) (v : G)
    (hzero : (1 : G) ∉ S)
    (hinv : ∀ ⦃x⦄, x ∈ S → x⁻¹ ∈ S) :
    ((SimpleGraph.mulCayley S).neighborSet v).ncard = S.ncard := by
  apply Set.ncard_congr (fun x _ => v⁻¹ * x)
  · intro x hx
    have hadj : (SimpleGraph.mulCayley S).Adj v x :=
      (SimpleGraph.mem_neighborSet _ _ _).mp hx
    rw [SimpleGraph.mulCayley_adj] at hadj
    rcases hadj with ⟨_, h | h⟩
    · exact h
    · simpa [mul_inv_rev] using hinv h
  · intro a b ha hb hab
    calc
      a = v * (v⁻¹ * a) := by simp
      _ = v * (v⁻¹ * b) := by rw [hab]
      _ = b := by simp
  · intro b hb
    refine ⟨v * b, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborSet, SimpleGraph.mulCayley_adj]
      refine ⟨?_, Or.inl ?_⟩
      · intro h
        have hb1 : (1 : G) = b := by
          calc
            1 = v⁻¹ * v := by simp
            _ = v⁻¹ * (v * b) := by rw [← h]
            _ = b := by simp
        apply hzero
        rw [hb1]
        exact hb
      · simpa using hb
    · simp

private lemma mulCayley_connected_of_closure_eq_top
    {G : Type*} [Group G] (S : Set G) (hS : Subgroup.closure S = ⊤) :
    (SimpleGraph.mulCayley S).Connected := by
  let leftMul (d : G) : SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S :=
    { toFun := fun x => d * x
      map_rel' := fun h => SimpleGraph.mulCayley_adj_mul_iff_right.mpr h }
  refine ⟨?_⟩
  intro u v
  let z := u⁻¹ * v
  have hz : z ∈ Subgroup.closure S := by
    rw [hS]
    trivial
  have hone_mem : ∀ z : G, z ∈ Subgroup.closure S →
      (SimpleGraph.mulCayley S).Reachable 1 z := by
    intro z hz'
    induction hz' using Subgroup.closure_induction with
    | mem x hx =>
        by_cases hx1 : x = 1
        · subst x
          exact SimpleGraph.Reachable.rfl
        · exact (SimpleGraph.mulCayley_adj S 1 x).mpr
            ⟨Ne.symm hx1, Or.inl (by simpa using hx)⟩ |>.reachable
    | one => exact SimpleGraph.Reachable.rfl
    | mul x y _ _ hx hy =>
        have hxy : (SimpleGraph.mulCayley S).Reachable x (x * y) := by
          simpa [leftMul] using hy.map (leftMul x)
        exact hx.trans hxy
    | inv x _ hx =>
        have hxi := hx.symm.map (leftMul x⁻¹)
        simpa [leftMul] using hxi
  have hone_z : (SimpleGraph.mulCayley S).Reachable 1 z := hone_mem z hz
  have huv := hone_z.map (leftMul u)
  simpa [z, leftMul, mul_assoc] using huv

private lemma mulCayley_connected_iff_closure_eq_top
    {G : Type*} [Group G] (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro h
    apply (Subgroup.eq_top_iff' (Subgroup.closure S)).2
    intro x
    let H : Subgroup G := Subgroup.closure S
    have hrel : ∀ {a b : G}, (SimpleGraph.mulCayley S).Adj a b → a⁻¹ * b ∈ H := by
      intro a b hab
      rw [SimpleGraph.mulCayley_adj] at hab
      rcases hab with ⟨_, hab | hba⟩
      · exact Subgroup.subset_closure hab
      · have : b⁻¹ * a ∈ H := Subgroup.subset_closure hba
        simpa using H.inv_mem this
    have hreach : ∀ {a b : G}, (SimpleGraph.mulCayley S).Reachable a b →
        a⁻¹ * b ∈ H := by
      intro a b hab
      rw [SimpleGraph.reachable_iff_reflTransGen] at hab
      induction hab with
      | refl => simpa using H.one_mem
      | @tail b c hab hbc ih =>
          have hstep := hrel hbc
          have hmul := H.mul_mem ih hstep
          simpa [mul_assoc] using hmul
    exact by simpa using hreach (h 1 x)
  · exact mulCayley_connected_of_closure_eq_top S

/-- Claim 27031: the valency and connectedness annotations are invariant in an
ordinary Cayley graph-isomorphism fiber. -/
theorem valency_and_connectedness_annotations_claim27031
    {G : Type*} [Fintype G] [Group G]
    (S T : Set G)
    (hSzero : (1 : G) ∉ S) (hTzero : (1 : G) ∉ T)
    (hSinv : ∀ ⦃x⦄, x ∈ S → x⁻¹ ∈ S)
    (hTinv : ∀ ⦃x⦄, x ∈ T → x⁻¹ ∈ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) :
    (∀ v : G, ((SimpleGraph.mulCayley S).neighborSet v).ncard = S.ncard) ∧
      (∀ v : G, ((SimpleGraph.mulCayley T).neighborSet v).ncard = T.ncard) ∧
      S.ncard = T.ncard ∧
      ((SimpleGraph.mulCayley S).Connected ↔
        (SimpleGraph.mulCayley T).Connected) ∧
      ((SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤) ∧
      ((SimpleGraph.mulCayley T).Connected ↔ Subgroup.closure T = ⊤) := by
  have hvalS : ∀ v : G, ((SimpleGraph.mulCayley S).neighborSet v).ncard = S.ncard :=
    fun v => mulCayley_neighborSet_ncard_eq S v hSzero hSinv
  have hvalT : ∀ v : G, ((SimpleGraph.mulCayley T).neighborSet v).ncard = T.ncard :=
    fun v => mulCayley_neighborSet_ncard_eq T v hTzero hTinv
  have himage : e '' (SimpleGraph.mulCayley S).neighborSet 1 =
      (SimpleGraph.mulCayley T).neighborSet (e 1) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [SimpleGraph.mem_neighborSet] at hv ⊢
      exact e.map_rel_iff.mpr hv
    · intro hw
      rw [SimpleGraph.mem_neighborSet] at hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      rw [SimpleGraph.mem_neighborSet]
      apply e.map_rel_iff.mp
      simpa using hw
  have hcard : S.ncard = T.ncard := by
    calc
      S.ncard = ((SimpleGraph.mulCayley S).neighborSet 1).ncard := (hvalS 1).symm
      _ = (e '' (SimpleGraph.mulCayley S).neighborSet 1).ncard :=
        (Set.ncard_image_of_injective _ e.injective).symm
      _ = ((SimpleGraph.mulCayley T).neighborSet (e 1)).ncard := by rw [himage]
      _ = T.ncard := hvalT (e 1)
  exact ⟨hvalS, hvalT, hcard, e.connected_iff,
    mulCayley_connected_iff_closure_eq_top S,
    mulCayley_connected_iff_closure_eq_top T⟩

end MathlibPlus.GraphTheory.Claim27031
