import MathlibPlus.Basic

namespace MathlibPlus.Algebra.ConjugacyOrientation

/-- The reciprocal-pair traces and quartic identities in claim 14760. -/
theorem orientationSquare
    (y α : ℂ) (hy : y ≠ 0) (hα : α ≠ 0) :
    let A : ℂ := y + y⁻¹
    let B : ℂ := α + α⁻¹
    let c : ℂ := (y - y⁻¹) * (α - α⁻¹)
    let r₁ : ℂ := y * α + y⁻¹ * α⁻¹
    let r₂ : ℂ := y * α⁻¹ + y⁻¹ * α
    let P : Polynomial ℂ :=
      1 - Polynomial.C (A * B) * Polynomial.X +
        Polynomial.C (A ^ 2 + B ^ 2 - 2) * Polynomial.X ^ 2 -
        Polynomial.C (A * B) * Polynomial.X ^ 3 + Polynomial.X ^ 4
    r₁ + r₂ = A * B ∧
      r₁ - r₂ = c ∧
      c ^ 2 = (A ^ 2 - 4) * (B ^ 2 - 4) ∧
      (1 - Polynomial.C r₁ * Polynomial.X + Polynomial.X ^ 2) *
          (1 - Polynomial.C r₂ * Polynomial.X + Polynomial.X ^ 2) = P := by
  dsimp
  have hsum :
      y * α + y⁻¹ * α⁻¹ + (y * α⁻¹ + y⁻¹ * α) =
        (y + y⁻¹) * (α + α⁻¹) := by
    ring
  have hprod :
      (y * α + y⁻¹ * α⁻¹) * (y * α⁻¹ + y⁻¹ * α) + 2 =
        (y + y⁻¹) ^ 2 + (α + α⁻¹) ^ 2 - 2 := by
    field_simp [hy, hα]
    ring
  have hpoly (u v : ℂ) :
      (1 - Polynomial.C u * Polynomial.X + Polynomial.X ^ 2) *
          (1 - Polynomial.C v * Polynomial.X + Polynomial.X ^ 2) =
        1 - Polynomial.C (u + v) * Polynomial.X +
            Polynomial.C (u * v + 2) * Polynomial.X ^ 2 -
          Polynomial.C (u + v) * Polynomial.X ^ 3 + Polynomial.X ^ 4 := by
    rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_mul,
      Polynomial.C_ofNat]
    ring
  refine ⟨hsum, by ring, ?_, ?_⟩
  · field_simp [hy, hα]
    ring
  · rw [hpoly, hsum, hprod]

/-- Swapping `y` with its inverse preserves `A` and the quartic but reverses
`c`; therefore the displayed data do not determine the orientation sign when
`c` is nonzero. -/
theorem orientationSignSwap
    (y α : ℂ) (_hy : y ≠ 0) (_hα : α ≠ 0)
    (hc : (y - y⁻¹) * (α - α⁻¹) ≠ 0) :
    let A : ℂ := y + y⁻¹
    let B : ℂ := α + α⁻¹
    let c : ℂ := (y - y⁻¹) * (α - α⁻¹)
    let P : Polynomial ℂ :=
      1 - Polynomial.C (A * B) * Polynomial.X +
        Polynomial.C (A ^ 2 + B ^ 2 - 2) * Polynomial.X ^ 2 -
        Polynomial.C (A * B) * Polynomial.X ^ 3 + Polynomial.X ^ 4
    let A' : ℂ := y⁻¹ + (y⁻¹)⁻¹
    let B' : ℂ := B
    let c' : ℂ := (y⁻¹ - (y⁻¹)⁻¹) * (α - α⁻¹)
    let P' : Polynomial ℂ :=
      1 - Polynomial.C (A' * B') * Polynomial.X +
        Polynomial.C (A' ^ 2 + B' ^ 2 - 2) * Polynomial.X ^ 2 -
        Polynomial.C (A' * B') * Polynomial.X ^ 3 + Polynomial.X ^ 4
    A' = A ∧ B' = B ∧ c' = -c ∧ c' ≠ c ∧ P' = P := by
  dsimp
  have hinvinv : (y⁻¹)⁻¹ = y := inv_inv y
  have hA : y⁻¹ + (y⁻¹)⁻¹ = y + y⁻¹ := by
    rw [hinvinv]
    ring
  have hc' : (y⁻¹ - (y⁻¹)⁻¹) * (α - α⁻¹) =
      -((y - y⁻¹) * (α - α⁻¹)) := by
    rw [hinvinv]
    ring
  refine ⟨hA, rfl, hc', ?_, ?_⟩
  · intro h
    apply hc
    have hneg : -((y - y⁻¹) * (α - α⁻¹)) =
        (y - y⁻¹) * (α - α⁻¹) := by
      rw [← hc', h]
    have hzero : (y - y⁻¹) * (α - α⁻¹) +
        (y - y⁻¹) * (α - α⁻¹) = 0 := by
      calc
        (y - y⁻¹) * (α - α⁻¹) + (y - y⁻¹) * (α - α⁻¹) =
            -((y - y⁻¹) * (α - α⁻¹)) +
              (y - y⁻¹) * (α - α⁻¹) := by rw [hneg]
        _ = 0 := neg_add_cancel _
    rcases mul_eq_zero.mp (show (2 : ℂ) *
        ((y - y⁻¹) * (α - α⁻¹)) = 0 by simpa [two_mul] using hzero) with htwo | hzero
    · norm_num at htwo
    · exact hzero
  · rw [hA]

end MathlibPlus.Algebra.ConjugacyOrientation
