import MathlibPlus.Basic

namespace MathlibPlus.Algebra.FiniteField.Claim39810

/-!
The source's normalized rows are represented only by their displayed polynomial
functions here.  The coefficient carrier is the exact finite parameter set
`𝔽₃ˣ × 𝔽₃³`; the geometric assertion that a row has the four-plane-star
property remains a source-specific boundary for fidelity review.
-/

abbrev Parameter := (ZMod 3)ˣ × ZMod 3 × ZMod 3 × ZMod 3

def starPolynomial (p : Parameter) : (ZMod 3) → (ZMod 3) → ZMod 3 :=
  fun v w => (p.1 : ZMod 3) * v * w + p.2.1 * v ^ 2 + p.2.2.1 * v + p.2.2.2 * w

/-- The displayed coefficient parametrization is injective as a function family. -/
theorem starPolynomial_injective : Function.Injective starPolynomial := by
  intro p p' h
  have h10 := congrFun (congrFun h (1 : ZMod 3)) (0 : ZMod 3)
  have h20 := congrFun (congrFun h (2 : ZMod 3)) (0 : ZMod 3)
  have h01 := congrFun (congrFun h (0 : ZMod 3)) (1 : ZMod 3)
  have h11 := congrFun (congrFun h (1 : ZMod 3)) (1 : ZMod 3)
  norm_num [starPolynomial] at h10 h20 h01 h11
  have h2 : (2 : ZMod 3) = -1 := by decide
  have h4 : (4 : ZMod 3) = 1 := by decide
  simp [h2, h4] at h20
  have h20sub : p.2.1 - p.2.2.1 = p'.2.1 - p'.2.2.1 := by
    simpa [sub_eq_add_neg] using h20
  have ha : p.2.1 = p'.2.1 := by
    calc
      p.2.1 = 2 * (p.2.1 + p.2.2.1) + 2 * (p.2.1 - p.2.2.1) := by
        ring_nf
        rw [h4]
        simp
      _ = 2 * (p'.2.1 + p'.2.2.1) + 2 * (p'.2.1 - p'.2.2.1) := by
        rw [h10, h20sub]
      _ = p'.2.1 := by
        ring_nf
        rw [h4]
        simp
  have hb : p.2.2.1 = p'.2.2.1 := by
    calc
      p.2.2.1 = 2 * (p.2.1 + p.2.2.1) - 2 * (p.2.1 - p.2.2.1) := by
        ring_nf
        rw [h4]
        simp
      _ = 2 * (p'.2.1 + p'.2.2.1) - 2 * (p'.2.1 - p'.2.2.1) := by
        rw [h10, h20sub]
      _ = p'.2.2.1 := by
        ring_nf
        rw [h4]
        simp
  have hd : p.2.2.2 = p'.2.2.2 := h01
  have hc : (p.1 : ZMod 3) = (p'.1 : ZMod 3) := by
    rw [hd] at h11
    linear_combination h11 - h10
  apply Prod.ext
  · apply Units.ext
    exact hc
  · apply Prod.ext
    · exact ha
    · apply Prod.ext
      · exact hb
      · exact hd

/-- The exact finite displayed locus has `2 · 3³ = 54` functions. -/
theorem starPolynomial_card : Fintype.card (Set.range starPolynomial) = 54 := by
  calc
    Fintype.card (Set.range starPolynomial) = Fintype.card Parameter :=
      (Fintype.card_congr
        (Equiv.ofInjective starPolynomial starPolynomial_injective)).symm
    _ = 54 := by decide

/-- The parameter count is the source's `2 · 3³` arithmetic receipt. -/
theorem parameter_card : Fintype.card Parameter = 2 * 3 ^ 3 := by
  decide

end MathlibPlus.Algebra.FiniteField.Claim39810
