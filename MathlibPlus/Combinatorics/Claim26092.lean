import Mathlib

namespace MathlibPlus.Combinatorics.Claim26092

/-!
A tripartite linear triangle packing is represented by a finite set of triples
with no repeated pair in any of the three color-pair projections.  This is the
edge-disjoint-triangle convention: a triangle is determined by its three
vertices, and sharing an edge is exactly repetition of one such pair.
-/

abbrev ABCTuple (A B C : Type*) := A × B × C

def pairAB {A B C : Type*} (x : ABCTuple A B C) : A × B := (x.1, x.2.1)

def pairBC {A B C : Type*} (x : ABCTuple A B C) : B × C := (x.2.1, x.2.2)

def pairCA {A B C : Type*} (x : ABCTuple A B C) : C × A := (x.2.2, x.1)

def IsLinearPacking
    {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Finset (ABCTuple A B C)) : Prop :=
  (∀ ⦃x y⦄, x ∈ T → y ∈ T → pairAB x = pairAB y → x = y) ∧
  (∀ ⦃x y⦄, x ∈ T → y ∈ T → pairBC x = pairBC y → x = y) ∧
  (∀ ⦃x y⦄, x ∈ T → y ∈ T → pairCA x = pairCA y → x = y)

/-- The three pair projections inject the triangles into the three possible
color-pair edge sets, giving the displayed `min(ab,bc,ca)` bound. -/
theorem card_le_pair_products_claim26092
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Finset (ABCTuple A B C)) (hT : IsLinearPacking T) :
    T.card ≤ min (Fintype.card A * Fintype.card B)
      (min (Fintype.card B * Fintype.card C)
        (Fintype.card C * Fintype.card A)) := by
  have hab : T.card ≤ Fintype.card A * Fintype.card B := by
    let f : {x // x ∈ T} → A × B := fun x => pairAB x.1
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact hT.1 x.property y.property hxy
    have hc := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_coe, Fintype.card_prod] using hc
  have hbc : T.card ≤ Fintype.card B * Fintype.card C := by
    let f : {x // x ∈ T} → B × C := fun x => pairBC x.1
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact hT.2.1 x.property y.property hxy
    have hc := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_coe, Fintype.card_prod] using hc
  have hca : T.card ≤ Fintype.card C * Fintype.card A := by
    let f : {x // x ∈ T} → C × A := fun x => pairCA x.1
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact hT.2.2 x.property y.property hxy
    have hc := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_coe, Fintype.card_prod] using hc
  exact le_min hab (le_min hbc hca)

/-- The balanced three-partite arithmetic corollary, with the floor taken in
`ℕ` after embedding the total color-class size into `ℝ`. -/
theorem card_le_floor_total_claim26092
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Finset (ABCTuple A B C)) (hT : IsLinearPacking T) :
    T.card ≤
      ⌊(((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) : ℝ) ^ 2) / 9⌋₊ := by
  have hp := card_le_pair_products_claim26092 T hT
  have hmin1 :
      ((min (Fintype.card A * Fintype.card B)
        (min (Fintype.card B * Fintype.card C)
          (Fintype.card C * Fintype.card A)) : ℕ) : ℝ) ≤
        (Fintype.card A : ℝ) * Fintype.card B := by
    exact_mod_cast (min_le_left _ _)
  have hmin2 :
      ((min (Fintype.card A * Fintype.card B)
        (min (Fintype.card B * Fintype.card C)
          (Fintype.card C * Fintype.card A)) : ℕ) : ℝ) ≤
        (Fintype.card B : ℝ) * Fintype.card C := by
    have h :
        min (Fintype.card A * Fintype.card B)
            (min (Fintype.card B * Fintype.card C)
              (Fintype.card C * Fintype.card A)) ≤
          Fintype.card B * Fintype.card C :=
      (min_le_right _ _).trans (min_le_left _ _)
    exact_mod_cast h
  have hmin3 :
      ((min (Fintype.card A * Fintype.card B)
        (min (Fintype.card B * Fintype.card C)
          (Fintype.card C * Fintype.card A)) : ℕ) : ℝ) ≤
        (Fintype.card C : ℝ) * Fintype.card A := by
    have h :
        min (Fintype.card A * Fintype.card B)
            (min (Fintype.card B * Fintype.card C)
              (Fintype.card C * Fintype.card A)) ≤
          Fintype.card C * Fintype.card A :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact_mod_cast h
  have hsq1 : 0 ≤ ((Fintype.card A : ℝ) - Fintype.card B) ^ 2 :=
    sq_nonneg _
  have hsq2 : 0 ≤ ((Fintype.card B : ℝ) - Fintype.card C) ^ 2 :=
    sq_nonneg _
  have hsq3 : 0 ≤ ((Fintype.card C : ℝ) - Fintype.card A) ^ 2 :=
    sq_nonneg _
  have hpair :
      (3 : ℝ) *
          ((Fintype.card A : ℝ) * Fintype.card B +
            Fintype.card B * Fintype.card C +
            Fintype.card C * Fintype.card A) ≤
        (Fintype.card A + Fintype.card B + Fintype.card C) ^ 2 := by
    nlinarith [hsq1, hsq2, hsq3]
  have hmin_sum :
      (3 : ℝ) *
          ((min (Fintype.card A * Fintype.card B)
            (min (Fintype.card B * Fintype.card C)
              (Fintype.card C * Fintype.card A)) : ℕ) : ℝ) ≤
        (Fintype.card A : ℝ) * Fintype.card B +
          Fintype.card B * Fintype.card C +
          Fintype.card C * Fintype.card A := by
    nlinarith [hmin1, hmin2, hmin3]
  have hmin_bound :
      (9 : ℝ) *
          ((min (Fintype.card A * Fintype.card B)
            (min (Fintype.card B * Fintype.card C)
              (Fintype.card C * Fintype.card A)) : ℕ) : ℝ) ≤
        ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) : ℝ) ^ 2 := by
    calc
      (9 : ℝ) *
          ((min (Fintype.card A * Fintype.card B)
            (min (Fintype.card B * Fintype.card C)
              (Fintype.card C * Fintype.card A)) : ℕ) : ℝ) =
          3 * (3 *
            ((min (Fintype.card A * Fintype.card B)
              (min (Fintype.card B * Fintype.card C)
                (Fintype.card C * Fintype.card A)) : ℕ) : ℝ)) := by ring
      _ ≤ 3 *
          ((Fintype.card A : ℝ) * Fintype.card B +
            Fintype.card B * Fintype.card C +
            Fintype.card C * Fintype.card A) := by
        nlinarith [hmin_sum]
      _ ≤ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) : ℝ) ^ 2 := by
        simpa [Nat.cast_add, Nat.cast_mul] using hpair
  have hcard_min :
      (T.card : ℝ) ≤
        ((min (Fintype.card A * Fintype.card B)
          (min (Fintype.card B * Fintype.card C)
            (Fintype.card C * Fintype.card A)) : ℕ) : ℝ) := by
    exact_mod_cast hp
  apply Nat.le_floor
  nlinarith

end MathlibPlus.Combinatorics.Claim26092
