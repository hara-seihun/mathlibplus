import Mathlib

namespace MathlibPlus.Combinatorics

open scoped BigOperators

private abbrev latinSquareVertex (k : ℕ) := Fin 3 × ZMod k

private def latinSquareTriangle {k : ℕ} [NeZero k]
    (i j : ZMod k) : Finset (latinSquareVertex k) :=
  {(0, i), (1, j), (2, i + j)}

private lemma latinSquareTriangle_card {k : ℕ} [NeZero k]
    (i j : ZMod k) : (latinSquareTriangle i j).card = 3 := by
  simp [latinSquareTriangle]

private lemma latinSquareTriangle_rainbow {k : ℕ} [NeZero k]
    (i j : ZMod k) :
    (latinSquareTriangle i j).image Prod.fst = (Finset.univ : Finset (Fin 3)) := by
  ext c
  fin_cases c <;> simp [latinSquareTriangle]

private def latinSquarePacking {k : ℕ} [NeZero k] :
    Finset (Finset (latinSquareVertex k)) :=
  (Finset.univ : Finset (ZMod k × ZMod k)).image
    (fun p => latinSquareTriangle p.1 p.2)

private lemma latinSquareTriangle_injective {k : ℕ} [NeZero k] :
    Function.Injective (fun p : ZMod k × ZMod k =>
      latinSquareTriangle p.1 p.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  change latinSquareTriangle i j = latinSquareTriangle i' j' at h
  have hi : (0, i) ∈ latinSquareTriangle i j := by
    simp [latinSquareTriangle]
  have hi' : (0, i) ∈ latinSquareTriangle i' j' := by
    rw [← h]
    exact hi
  have hii : i = i' := by simpa [latinSquareTriangle] using hi'
  have hj : (1, j) ∈ latinSquareTriangle i j := by
    simp [latinSquareTriangle]
  have hj' : (1, j) ∈ latinSquareTriangle i' j' := by
    rw [← h]
    exact hj
  have hjj : j = j' := by simpa [latinSquareTriangle] using hj'
  exact Prod.ext hii hjj

private lemma latinSquarePacking_card {k : ℕ} [NeZero k] :
    (latinSquarePacking (k := k)).card = k ^ 2 := by
  change ((Finset.univ : Finset (ZMod k × ZMod k)).image
      (fun p => latinSquareTriangle p.1 p.2)).card = k ^ 2
  rw [Finset.card_image_of_injective _ latinSquareTriangle_injective]
  simp [Fintype.card_prod, pow_two]

private def latinSquareUsed {k : ℕ} [NeZero k] :
    Finset (latinSquareVertex k) :=
  (latinSquarePacking (k := k)).biUnion id

private lemma latinSquareUsed_eq_univ {k : ℕ} [NeZero k] :
    latinSquareUsed (k := k) = Finset.univ := by
  ext v
  constructor
  · intro hv
    simp
  · intro hv
    have hv' : v.1 = 0 ∨ v.1 = 1 ∨ v.1 = 2 := by
      generalize hc : v.1 = c
      fin_cases c <;> simp_all
    rcases hv' with hc | hc | hc
    · have hv0 : v = (0, v.2) := Prod.ext hc rfl
      have hm : latinSquareTriangle v.2 0 ∈ latinSquarePacking (k := k) := by
        simp [latinSquarePacking]
      have hmem : v ∈ latinSquareTriangle v.2 0 := by
        rw [hv0]
        simp [latinSquareTriangle]
      exact Finset.mem_biUnion.mpr
        ⟨latinSquareTriangle v.2 0, hm, hmem⟩
    · have hv1 : v = (1, v.2) := Prod.ext hc rfl
      have hm : latinSquareTriangle 0 v.2 ∈ latinSquarePacking (k := k) := by
        simp [latinSquarePacking]
      have hmem : v ∈ latinSquareTriangle 0 v.2 := by
        rw [hv1]
        simp [latinSquareTriangle]
      exact Finset.mem_biUnion.mpr
        ⟨latinSquareTriangle 0 v.2, hm, hmem⟩
    · have hv2 : v = (2, v.2) := Prod.ext hc rfl
      have hm : latinSquareTriangle 0 v.2 ∈ latinSquarePacking (k := k) := by
        simp [latinSquarePacking]
      have hmem : v ∈ latinSquareTriangle 0 v.2 := by
        rw [hv2]
        simp [latinSquareTriangle]
      exact Finset.mem_biUnion.mpr
        ⟨latinSquareTriangle 0 v.2, hm, hmem⟩

private lemma latinSquareUsed_card {k : ℕ} [NeZero k] :
    (latinSquareUsed (k := k)).card = 3 * k := by
  rw [latinSquareUsed_eq_univ]
  simp [Fintype.card_prod, ZMod.card]

private lemma latinSquare_density_identity (k : ℕ) :
    k ^ 2 = (3 * k) ^ 2 / 9 := by
  rw [show (3 * k) ^ 2 = 9 * k ^ 2 by ring]
  simpa [Nat.mul_comm] using
    (Nat.mul_div_cancel_left (k ^ 2) (by norm_num : 0 < 9))

private def latinSquareColorSupport {k : ℕ} [NeZero k]
    (v : latinSquareVertex k) : Finset (Fin 3) :=
  (Finset.univ : Finset (Fin 3)).filter
    (fun c => ∃ T ∈ latinSquarePacking (k := k), v ∈ T ∧ c = v.1)

private lemma latinSquareColorSupport_eq_singleton {k : ℕ} [NeZero k]
    (v : latinSquareVertex k) :
    latinSquareColorSupport v = {v.1} := by
  ext c
  simp only [latinSquareColorSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨T, hT, hvT, hc⟩
    exact hc
  · intro hc
    have hv : v ∈ latinSquareUsed (k := k) := by
      rw [latinSquareUsed_eq_univ]
      simp
    rcases Finset.mem_biUnion.mp hv with ⟨T, hT, hvT⟩
    exact ⟨T, hT, hvT, hc⟩

private def latinSquareDebt {k : ℕ} [NeZero k] : ℕ :=
  ∑ v : latinSquareVertex k, ((latinSquareColorSupport v).card - 1)

private lemma latinSquareDebt_zero {k : ℕ} [NeZero k] :
    latinSquareDebt (k := k) = 0 := by
  simp [latinSquareDebt, latinSquareColorSupport_eq_singleton]

private lemma latinSquareTriangle_inter_card_le_one {k : ℕ} [NeZero k]
    {i j i' j' : ZMod k} (hpair : (i, j) ≠ (i', j')) :
    (latinSquareTriangle i j ∩ latinSquareTriangle i' j').card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro x y hx hy
  have hxmem : x ∈ latinSquareTriangle i j ∧
      x ∈ latinSquareTriangle i' j' := Finset.mem_inter.mp hx
  have hymem : y ∈ latinSquareTriangle i j ∧
      y ∈ latinSquareTriangle i' j' := Finset.mem_inter.mp hy
  have hx₁ : x = (0, i) ∨ x = (1, j) ∨ x = (2, i + j) := by
    simpa [latinSquareTriangle] using hxmem.1
  have hx₂ : x = (0, i') ∨ x = (1, j') ∨ x = (2, i' + j') := by
    simpa [latinSquareTriangle] using hxmem.2
  have hy₁ : y = (0, i) ∨ y = (1, j) ∨ y = (2, i + j) := by
    simpa [latinSquareTriangle] using hymem.1
  have hy₂ : y = (0, i') ∨ y = (1, j') ∨ y = (2, i' + j') := by
    simpa [latinSquareTriangle] using hymem.2
  rcases hx₁ with hx₁ | hx₁ | hx₁ <;> subst x
  rcases hy₁ with hy₁ | hy₁ | hy₁ <;> subst y
  all_goals
    rcases hx₂ with hx₂ | hx₂ | hx₂
    all_goals
      rcases hy₂ with hy₂ | hy₂ | hy₂
      all_goals simp_all [Prod.ext_iff]

/--
The Latin-square sharpness construction from claim 26096.  The three color
classes are `Fin 3 × ZMod k`, the indexed triangles are
`{(0,i),(1,j),(2,i+j)}`, and `latinSquareDebt` is the sum of the excesses
`|C(V)| - 1` for the colors carried by each used vertex.

`NeZero k` is the exact finite cyclic-group encoding of the source condition
`k ≥ 1`.
-/
theorem latinSquareSharpnessConstruction_claim26096 (k : ℕ) [NeZero k] :
    (∀ i j : ZMod k, (latinSquareTriangle i j).card = 3) ∧
    (∀ i j : ZMod k,
      (latinSquareTriangle i j).image Prod.fst =
        (Finset.univ : Finset (Fin 3))) ∧
    (latinSquarePacking (k := k)).card = k ^ 2 ∧
    (latinSquareUsed (k := k)).card = 3 * k ∧
    k ^ 2 = (3 * k) ^ 2 / 9 ∧
    latinSquareDebt (k := k) = 0 ∧
    (∀ i j i' j' : ZMod k, (i, j) ≠ (i', j') →
      (latinSquareTriangle i j ∩ latinSquareTriangle i' j').card ≤ 1) := by
  refine ⟨fun i j => latinSquareTriangle_card i j,
    fun i j => latinSquareTriangle_rainbow i j,
    latinSquarePacking_card, latinSquareUsed_card,
    latinSquare_density_identity k, latinSquareDebt_zero, ?_⟩
  exact fun i j i' j' h => latinSquareTriangle_inter_card_le_one h

end MathlibPlus.Combinatorics
