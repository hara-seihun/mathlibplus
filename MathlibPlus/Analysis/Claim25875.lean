import Mathlib

namespace MathlibPlus.Analysis.R0478

/-- The exact three vertex values of a normalized degree-two coefficient
 direction at the interior node `u` and ordering point `x`. -/
noncomputable def coefficientDirectionVertexValues25874
    (u x : ℝ) (a b : ℤ) : Fin 3 → ℝ :=
  ![0, (a : ℝ) - (b : ℝ) / x, (a : ℝ) - (b : ℝ) / u]

/-- The max-minus-min lattice width of that coefficient direction. -/
noncomputable def coefficientWidth25874 (u x : ℝ) (a b : ℤ) : ℝ :=
  let v := coefficientDirectionVertexValues25874 u x a b
  (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty v -
    (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty v

/-- Claim 25875: the constant and primitive leading coefficient directions
have the exact normalized widths on the repaired Boyd simplex carrier. -/
noncomputable def exactConstantAndLeadingWidths_claim25875 : Prop :=
  ∀ x : ℝ, 6 < x →
    let u : ℝ := (1 - Real.sqrt 17) / 2
    coefficientWidth25874 u x 1 0 = 1 ∧
      coefficientWidth25874 u x 0 1 =
        1 / x - 1 / u ∧
      coefficientWidth25874 u x 0 1 =
        1 / x + (Real.sqrt 17 + 1) / 8

end MathlibPlus.Analysis.R0478
