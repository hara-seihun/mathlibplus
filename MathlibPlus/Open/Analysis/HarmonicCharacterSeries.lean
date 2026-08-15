import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

/-- The harmonic character of the `k`th symmetric-power torus representation. -/
noncomputable def harmonicCharacter (k : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (k + 1), z ^ ((k : ℤ) - (2 : ℤ) * (r : ℤ))

/-- The mixed harmonic module in its torus weight basis, indexed by the `(k+1)²` grid. -/
noncomputable def mixedHarmonicTorusAction (k : ℕ) (y α : ℂ) :
    Matrix (Fin (k + 1) × Fin (k + 1)) (Fin (k + 1) × Fin (k + 1)) ℂ :=
  Matrix.diagonal (fun i : Fin (k + 1) × Fin (k + 1) =>
    y ^ ((k : ℤ) - (2 : ℤ) * (i.1.val : ℤ)) *
      α ^ ((k : ℤ) - (2 : ℤ) * (i.2.val : ℤ)))

/--
The admitted harmonic character and generating-series claim.  The generating
series is represented as a formal power series in `PowerSeries ℂ`, so the
 displayed sum is the coefficient sequence in the formal variable `X`.
-/
noncomputable def harmonicCharacterSeries : Prop :=
  ∀ (y α : ℂ), y ≠ 0 → α ≠ 0 →
    (∀ k : ℕ,
      Matrix.trace (mixedHarmonicTorusAction k y α) =
        harmonicCharacter k y * harmonicCharacter k α) ∧
    (PowerSeries.mk (fun k : ℕ =>
        harmonicCharacter k y * harmonicCharacter k α) =
      ((1 : PowerSeries ℂ) - PowerSeries.X ^ 2) *
        (∏ ε ∈ ({(-1 : ℤ), 1} : Finset ℤ),
          ∏ δ ∈ ({(-1 : ℤ), 1} : Finset ℤ),
            (1 - PowerSeries.C (y ^ ε * α ^ δ) * PowerSeries.X))⁻¹)

end MathlibPlus.Open
