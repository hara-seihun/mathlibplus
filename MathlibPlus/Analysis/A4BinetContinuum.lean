import Mathlib

/-!
# Two-correction Binet continuum data

Formalization of admitted claim 312.
-/

open MeasureTheory

namespace MathlibPlus.Analysis.A4Binet

/-- The elementary function `c` displayed in claim 312 is exactly the derivative
of the displayed two-correction Binet function `b`. The source only uses `u ≥ 0`;
the identity in fact holds on all of `ℝ`. -/
theorem twoCorrectionBinet_hasDerivAt (u : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦
        1 / 4 + u * Real.exp u + Real.exp (-u) *
          (4 / 45 * u ^ 4 - 1 / 3 * u ^ 2 + 1 / 2 * u - 1 / 4))
      ((u + 1) * Real.exp u + Real.exp (-u) *
        (-4 / 45 * u ^ 4 + 16 / 45 * u ^ 3 + 1 / 3 * u ^ 2 - 7 / 6 * u + 3 / 4)) u := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u := by
    convert (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u) using 1 <;>
      first | rfl | simp
  have hp : HasDerivAt
      (fun x : ℝ => 4 / 45 * x ^ 4 - 1 / 3 * x ^ 2 + 1 / 2 * x - 1 / 4)
      (16 / 45 * u ^ 3 - 2 / 3 * u + 1 / 2) u := by
    convert (((hasDerivAt_pow 4 u).const_mul (4 / 45 : ℝ)).sub
      ((hasDerivAt_pow 2 u).const_mul (1 / 3 : ℝ))).add
      ((hasDerivAt_id u).const_mul (1 / 2 : ℝ)) |>.sub_const (1 / 4 : ℝ) using 1 <;>
      first | rfl | (norm_num; ring)
  convert (hasDerivAt_const u (1 / 4 : ℝ)).add
    (((hasDerivAt_id u).mul (Real.hasDerivAt_exp u)).add (he.mul hp)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring) | (ext x; dsimp; ring)

end MathlibPlus.Analysis.A4Binet

namespace MathlibPlus.Open.Analysis.A4Binet

/-- On `L²(0, α)`, the kernel `K(x,y)=c(x+y)+c(|x-y|)` from claim 312 defines a
bounded operator, and `A=(1/2)I-K`. The existential continuous linear map is
pinned to the displayed integral action on the canonical `Lp` representative. -/
def twoCorrectionBinetContinuumOperator : Prop :=
  let c : ℝ → ℝ := fun u ↦
    (u + 1) * Real.exp u + Real.exp (-u) *
      (-4 / 45 * u ^ 4 + 16 / 45 * u ^ 3 + 1 / 3 * u ^ 2 - 7 / 6 * u + 3 / 4)
  ∀ α : ℝ, 0 < α →
    let μ : Measure ℝ := volume.restrict (Set.Icc 0 α)
    ∃ A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      ∀ f : Lp ℝ 2 μ,
        let g : ℝ → ℝ := fun x ↦
          (1 / 2) * f x - ∫ y,
            (c (x + y) + c |x - y|) * f y ∂μ
        ∃ hg : MemLp g 2 μ, A f = hg.toLp g

end MathlibPlus.Open.Analysis.A4Binet
