import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/--
For a Gamma law with positive integer shape, the even-moment evaluation
matrix at positive, strictly increasing points has positive determinant;
the same conclusion holds on the indicated logarithmic integer intervals.
-/
def gamma_even_appell_positive_integer_shape_global_chebyshev : Prop :=
  ∀ (q : ℕ) (θ : ℝ),
    1 ≤ q → 0 < θ →
      let gammaLaw : MeasureTheory.Measure ℝ :=
        MeasureTheory.Measure.withDensity MeasureTheory.volume
          (ProbabilityTheory.gammaPDF (q : ℝ) θ)
      let P : ℝ → ℕ → ℝ :=
        fun y j =>
          MeasureTheory.integral gammaLaw (fun z : ℝ => (y + z) ^ (2 * j))
      ( (∀ (r : ℕ), 1 ≤ r →
            ∀ (y : ℕ → ℝ),
              (0 < y 0 ∧
                ∀ (i j : Fin r), i.val < j.val → y i.val < y j.val) →
                0 < Matrix.det (fun i j : Fin r => P (y i.val) j.val))
        ∧
        (∀ (r : ℕ), 1 ≤ r →
          ∀ (n : ℕ → ℕ) (y : ℕ → ℝ),
            (0 < n 0 ∧
              (∀ (i j : Fin r), i.val < j.val → n i.val < n j.val) ∧
              ∀ (i : Fin r),
                Real.log (n i.val : ℝ) < y i.val ∧
                  y i.val < Real.log ((n i.val + 1 : ℕ) : ℝ)) →
            0 < Matrix.det (fun i j : Fin r => P (y i.val) j.val)))

end MathlibPlus.Open.Analysis
