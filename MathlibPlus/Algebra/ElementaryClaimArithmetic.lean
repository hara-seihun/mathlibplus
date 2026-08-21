import MathlibPlus.Basic

namespace MathlibPlus.Algebra.ExponentCancellation

/-- Claim 18072's exponent calculation, over the rationals. -/
theorem changeOfVariablesExponent :
    (2 : ℚ) * (5 / 4) - 3 / 2 = 1 := by
  norm_num

end MathlibPlus.Algebra.ExponentCancellation

namespace MathlibPlus.Algebra.PatelYangPropagation

/--
Claim 21987's corrected propagation inequality.  The powers are Lean's real
`rpow`s, so the positivity hypotheses and the exponent arithmetic are explicit.
-/
theorem correctedPropagation {a theta₂ T : ℝ}
    (_ha : 0 < a) (hθ : 0 < theta₂) (hT : 0 < T)
    (h : theta₂ * T ^ (7 / 17 : ℝ) < a) :
    theta₂ ^ (36 / 41 : ℝ) * T ^ (65 / 697 : ℝ) <
      a ^ (36 / 41 : ℝ) * T ^ (-11 / 41 : ℝ) := by
  have hp : (0 : ℝ) < 36 / 41 := by norm_num
  have hbase : 0 ≤ theta₂ * T ^ (7 / 17 : ℝ) := by
    positivity
  have hpow := Real.rpow_lt_rpow hbase h hp
  have hmul : 0 < T ^ (-11 / 41 : ℝ) := Real.rpow_pos_of_pos hT _
  have hscaled := (mul_lt_mul_of_pos_right hpow hmul)
  rw [Real.mul_rpow (le_of_lt hθ) (le_of_lt (Real.rpow_pos_of_pos hT _)),
    ← Real.rpow_mul (le_of_lt hT)] at hscaled
  have hexp : (7 / 17 : ℝ) * (36 / 41) + (-11 / 41) = 65 / 697 := by
    norm_num
  rw [mul_assoc, ← Real.rpow_add hT] at hscaled
  rw [hexp] at hscaled
  exact hscaled

end MathlibPlus.Algebra.PatelYangPropagation


namespace MathlibPlus.Algebra.OrderedPairCount

/-!
Claim 41129 says only "ordered pairs" and does not specify the ambient
number system.  This declaration records the natural-number interpretation:
`a` ranges over `Icc 3 100` and `b` over `Ico 2 (3*a^2)`.  The ambiguity is
reported in the admission summary rather than hidden in the encoding.
-/
theorem orderedPairCount :
    ((Finset.Icc 3 100).biUnion (fun a =>
      (Finset.Ico 2 (3 * a ^ 2)).image (fun b => (a, b)))).card =
      1014839 := by
  have card_fiber (a : ℕ) :
      ((Finset.Ico 2 (3 * a ^ 2)).image (fun b => (a, b))).card =
        3 * a ^ 2 - 2 := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      simpa using congrArg Prod.snd hxy
  have disjoint_fibers :
      (↑(Finset.Icc 3 100) : Set ℕ).PairwiseDisjoint (fun a =>
        (Finset.Ico 2 (3 * a ^ 2)).image (fun b => (a, b))) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro a ha b hb hab
    rcases hab with ⟨x, hx⟩
    have hxa : x ∈ (Finset.Ico 2 (3 * a ^ 2)).image (fun y => (a, y)) :=
      (Finset.mem_inter.mp hx).1
    have hxb : x ∈ (Finset.Ico 2 (3 * b ^ 2)).image (fun y => (b, y)) :=
      (Finset.mem_inter.mp hx).2
    have hxa' : x.1 = a := by
      simp only [Finset.mem_image] at hxa
      obtain ⟨y, hy, rfl⟩ := hxa
      rfl
    have hxb' : x.1 = b := by
      simp only [Finset.mem_image] at hxb
      obtain ⟨y, hy, rfl⟩ := hxb
      rfl
    exact hxa'.symm.trans hxb'
  rw [Finset.card_biUnion disjoint_fibers]
  simp_rw [card_fiber]
  norm_num [Finset.sum_Icc_succ_top]

end MathlibPlus.Algebra.OrderedPairCount
