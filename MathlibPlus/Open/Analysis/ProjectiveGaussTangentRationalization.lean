import Mathlib

namespace MathlibPlus.Open.Analysis.ProjectiveGauss

open scoped BigOperators

/-- Claim 574: exact physical tangent rationalization for the folded reciprocal
heat kernel.  The three tangent coordinates are quadratic-over-square in the
independent activity, and the cleared three-tangent determinant has every one
of the 27 triquadratic activity sectors.

The sector coefficients are functions of the three row parameters and `l`;
being nonzero means not being the zero coefficient function, rather than being
nonzero after every specialization (collision specializations necessarily
vanish). -/
def exactPhysicalTangentRationalization : Prop :=
  let activity : ℝ → ℝ → ℝ := fun q l ↦
    l ^ (5 / 2 : ℝ) * Real.exp (-q * (l - l⁻¹))
  let jetChart : ℝ → ℝ → ℝ → Fin 3 → ℝ := fun q l h ↦
    let minusHeat := q / l
    let plusHeat := q * l
    let minusLog := minusHeat - 5 / 4
    let plusLog := 5 / 4 - plusHeat
    let minusJet : Fin 3 → ℝ :=
      ![minusLog,
        minusLog ^ 2 - minusHeat,
        minusLog ^ 3 - 3 * minusLog * minusHeat + minusHeat]
    let plusJet : Fin 3 → ℝ :=
      ![plusLog,
        plusLog ^ 2 - plusHeat,
        plusLog ^ 3 - 3 * plusLog * plusHeat - plusHeat]
    fun i ↦ (minusJet i + h * plusJet i) / (1 + h)
  let tangentChart : ℝ → ℝ → ℝ → Fin 3 → ℝ := fun q l h i ↦
    deriv (fun x ↦ jetChart x l h i) q -
      (l - l⁻¹) * h * deriv (fun u ↦ jetChart q l u i) h
  let gaussJet : ℝ → ℝ → Fin 3 → ℝ := fun q l ↦
    jetChart q l (activity q l)
  (∀ (q l : ℝ), 1 < l → ∀ i : Fin 3,
      tangentChart q l (activity q l) i =
        deriv (fun x ↦ gaussJet x l i) q) ∧
    ∃ coordinateCoeff : Fin 3 → Fin 3 → ℝ → ℝ → ℝ,
      (∀ (q l h : ℝ), 1 < l → 0 < h → ∀ i : Fin 3,
        tangentChart q l h i =
          (∑ degree : Fin 3,
              coordinateCoeff i degree q l * h ^ degree.val) /
            (1 + h) ^ 2) ∧
      ∃ sectorCoeff : (Fin 3 → Fin 3) → (Fin 3 → ℝ) → ℝ → ℝ,
        (∀ exponent : Fin 3 → Fin 3,
          ∃ (q : Fin 3 → ℝ) (l : ℝ),
            1 < l ∧ sectorCoeff exponent q l ≠ 0) ∧
        ∀ (q h : Fin 3 → ℝ) (l : ℝ),
          1 < l → (∀ i, 0 < h i) →
            Matrix.det (fun i j ↦ tangentChart (q j) l (h j) i) =
              (∑ exponent : Fin 3 → Fin 3,
                  sectorCoeff exponent q l *
                    ∏ i : Fin 3, h i ^ (exponent i).val) /
                (16 * l ^ 9 * ∏ i : Fin 3, (1 + h i) ^ 2)

end MathlibPlus.Open.Analysis.ProjectiveGauss
