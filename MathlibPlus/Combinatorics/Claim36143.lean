import Mathlib

namespace MathlibPlus.Combinatorics

abbrev Point_claim36143 := ℝ × ℝ

noncomputable def hingedL_claim36143 (k : ℕ) : ℕ := 4 * k + 4

noncomputable def basePoint_claim36143 (t : Fin (hingedL_claim36143 k + 1)) :
    Point_claim36143 := ((t.1 : ℝ), 0)

noncomputable def basePoints_claim36143 (k : ℕ) : Finset Point_claim36143 :=
  Finset.univ.image (fun t : Fin (hingedL_claim36143 k + 1) =>
    basePoint_claim36143 t)

noncomputable def upperPoint_claim36143
    {k : ℕ} (a : Fin k → ℝ) (r : Fin k) (b : Fin 2) : Point_claim36143 :=
  (4 * (r.1 : ℝ) + 2 + (b.1 : ℝ) + a r,
    Real.sqrt (1 - (a r) ^ 2))

noncomputable def upperPoints_claim36143
    (k : ℕ) (a : Fin k → ℝ) : Finset Point_claim36143 :=
  (Finset.univ.product (Finset.univ : Finset (Fin 2))).image
    (fun z : Fin k × Fin 2 => upperPoint_claim36143 a z.1 z.2)

noncomputable def hingedConfiguration_claim36143
    (k : ℕ) (a : Fin k → ℝ) : Finset Point_claim36143 :=
  basePoints_claim36143 k ∪ upperPoints_claim36143 k a

lemma basePoint_injective_claim36143 (k : ℕ) :
    Function.Injective (fun t : Fin (hingedL_claim36143 k + 1) =>
      basePoint_claim36143 t) := by
  intro r s h
  apply Fin.ext
  have hcoord : (r.1 : ℝ) = (s.1 : ℝ) := by
    simpa [basePoint_claim36143] using congrArg Prod.fst h
  exact_mod_cast hcoord

lemma basePoints_card_claim36143 (k : ℕ) :
    (basePoints_claim36143 k).card = hingedL_claim36143 k + 1 := by
  unfold basePoints_claim36143
  rw [Finset.card_image_of_injective _ (basePoint_injective_claim36143 k)]
  simp

lemma upperPoint_injective_claim36143
    (k : ℕ) (a : Fin k → ℝ)
    (ha : ∀ r, (1 : ℝ) / 10 < a r ∧ a r < 1 / 5) :
    Function.Injective (fun z : Fin k × Fin 2 => upperPoint_claim36143 a z.1 z.2) := by
  intro z w hzw
  have hx : 4 * (z.1.1 : ℝ) + 2 + (z.2.1 : ℝ) + a z.1 =
      4 * (w.1.1 : ℝ) + 2 + (w.2.1 : ℝ) + a w.1 := by
    simpa [upperPoint_claim36143] using congrArg Prod.fst hzw
  by_cases hrs : z.1 = w.1
  · apply Prod.ext hrs
    apply Fin.ext
    have hbc := hx
    rw [hrs] at hbc
    exact_mod_cast (by linarith : (z.2.1 : ℝ) = (w.2.1 : ℝ))
  · have hsep (hsmall : (z.1.1 + 1 : ℕ) ≤ w.1.1) :
        4 * (z.1.1 : ℝ) + 2 + (z.2.1 : ℝ) + a z.1 <
          4 * (w.1.1 : ℝ) + 2 + (w.2.1 : ℝ) + a w.1 := by
      have hnat : (z.1.1 : ℝ) + 1 ≤ (w.1.1 : ℝ) := by
        exact_mod_cast hsmall
      have hz := ha z.1
      have hw := ha w.1
      have hz2nat : z.2.1 ≤ 1 := by omega
      have hz2 : (z.2.1 : ℝ) ≤ 1 := by exact_mod_cast hz2nat
      have hw0 : (0 : ℝ) ≤ w.2.1 := by positivity
      linarith
    have hor : z.1.1 < w.1.1 ∨ w.1.1 < z.1.1 := by omega
    rcases hor with hlt | hgt
    · have hsmall : (z.1.1 + 1 : ℕ) ≤ w.1.1 := by omega
      exfalso
      exact (ne_of_lt (hsep hsmall)) hx
    · have hsmall : (w.1.1 + 1 : ℕ) ≤ z.1.1 := by omega
      have hrev :
          4 * (w.1.1 : ℝ) + 2 + (w.2.1 : ℝ) + a w.1 <
            4 * (z.1.1 : ℝ) + 2 + (z.2.1 : ℝ) + a z.1 := by
        have hnat : (w.1.1 : ℝ) + 1 ≤ (z.1.1 : ℝ) := by
          exact_mod_cast hsmall
        have hw := ha w.1
        have hz := ha z.1
        have hw2 : (w.2.1 : ℝ) ≤ 1 := by
          have : w.2.1 ≤ 1 := by omega
          exact_mod_cast this
        have hz0 : (0 : ℝ) ≤ z.2.1 := by positivity
        linarith
      exfalso
      exact (ne_of_lt hrev) hx.symm

lemma upperPoints_card_claim36143
    (k : ℕ) (a : Fin k → ℝ)
    (ha : ∀ r, (1 : ℝ) / 10 < a r ∧ a r < 1 / 5) :
    (upperPoints_claim36143 k a).card = 2 * k := by
  unfold upperPoints_claim36143
  rw [Finset.card_image_of_injective _ (upperPoint_injective_claim36143 k a ha)]
  simp [Nat.mul_comm]

lemma base_upper_disjoint_claim36143
    (k : ℕ) (a : Fin k → ℝ)
    (ha : ∀ r, (1 : ℝ) / 10 < a r ∧ a r < 1 / 5) :
    Disjoint (basePoints_claim36143 k) (upperPoints_claim36143 k a) := by
  rw [Finset.disjoint_left]
  intro x hxbase hxupper
  rcases Finset.mem_image.mp hxupper with ⟨z, hz, rfl⟩
  rcases Finset.mem_image.mp hxbase with ⟨t, ht, hxt⟩
  have hy : 0 < Real.sqrt (1 - (a z.1) ^ 2) := by
    apply Real.sqrt_pos.2
    have hzA := ha z.1
    nlinarith
  have hy0 : (upperPoint_claim36143 a z.1 z.2).2 = 0 := by
    simpa [basePoint_claim36143] using (congrArg Prod.snd hxt).symm
  exact (ne_of_gt hy) hy0

/-- The hinged-rhombus construction in claim 36143 has exactly `6k+5`
points.  Points are represented in the plane `ℝ × ℝ`; the construction keeps
`L=4k+4`, the unit base path, both points over each `s_r`, and the exact
interval constraints on every `a_r`. -/
theorem claim36143_hinged_configuration_card
    (k : ℕ) (hk : 1 ≤ k) (a : Fin k → ℝ)
    (ha : ∀ r, (1 : ℝ) / 10 < a r ∧ a r < 1 / 5) :
    (hingedConfiguration_claim36143 k a).card = 6 * k + 5 := by
  unfold hingedConfiguration_claim36143
  rw [Finset.card_union_of_disjoint (base_upper_disjoint_claim36143 k a ha),
    basePoints_card_claim36143, upperPoints_card_claim36143 k a ha]
  simp [hingedL_claim36143]
  omega

end MathlibPlus.Combinatorics
