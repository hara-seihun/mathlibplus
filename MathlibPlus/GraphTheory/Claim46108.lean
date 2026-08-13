import Mathlib

namespace MathlibPlus.GraphTheory.Claim46108

private theorem card_coord_zero
    (n : ℕ) (i : Fin n) :
    Fintype.card {x : Fin n → ZMod 2 // x i = 0} = 2 ^ (n - 1) := by
  let T := {j : Fin n // j ≠ i}
  let e0 := Equiv.funSplitAt i (ZMod 2)
  let e : {x : Fin n → ZMod 2 // x i = 0} ≃ (T → ZMod 2) :=
    { toFun := fun x => (e0 x.1).2
      invFun := fun g => ⟨e0.symm (0, g), by
        simp [e0, Equiv.funSplitAt, Equiv.piSplitAt]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext j
        by_cases h : j = i
        · subst j
          simp [e0, Equiv.funSplitAt, Equiv.piSplitAt, x.2]
        · simp [e0, Equiv.funSplitAt, Equiv.piSplitAt, h]
      right_inv := by
        intro g
        funext j
        simp [e0, Equiv.funSplitAt, Equiv.piSplitAt, j.property] }
  rw [Fintype.card_congr e]
  rw [Fintype.card_fun]
  rw [ZMod.card]
  have hT : Fintype.card T = n - 1 := by
    dsimp [T]
    rw [Fintype.card_subtype_compl (fun j : Fin n => j = i)]
    simp
  rw [hT]

/--
Claim 46108 (counting core).  For an affine family of Boolean-cube edge
indicators, the total oriented edge count is the half-cube size times the sum
of the coordinate averages.  The direction-i indicators are represented on
`Ω i = {x : Fin n → ZMod 2 // x i = 0}`, the canonical endpoint of a
direction-i edge.
-/
theorem claim46108_edgeCount_eq_halfCube_mul_sum_average
    (n : ℕ)
    (f : ∀ i : Fin n, {x : Fin n → ZMod 2 // x i = 0} → ZMod 2)
    (b : Fin n → ZMod 2)
    (a : Fin n → Fin n → ZMod 2)
    (ha : ∀ i : Fin n, a i i = 0)
    (h_affine :
      ∀ (i : Fin n) (x : {x : Fin n → ZMod 2 // x i = 0}),
        f i x = b i + ∑ k : Fin n, a i k * x.1 k) :
    (∑ i : Fin n,
        ((Finset.univ.filter (fun x => f i x = 1)).card : ℚ)) =
      (2 : ℚ) ^ (n - 1) *
        ∑ i : Fin n,
          (((Finset.univ.filter (fun x => f i x = 1)).card : ℚ) /
            (Fintype.card {x : Fin n → ZMod 2 // x i = 0} : ℚ)) := by
  classical
  have hpow : (2 : ℚ) ^ (n - 1) ≠ 0 := by positivity
  have hcard : ∀ i : Fin n,
      Fintype.card {x : Fin n → ZMod 2 // x i = 0} = 2 ^ (n - 1) := by
    intro i
    exact card_coord_zero n i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcard i]
  norm_num [Nat.cast_pow]
  field_simp

end MathlibPlus.GraphTheory.Claim46108
