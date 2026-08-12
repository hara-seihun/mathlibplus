import Mathlib

namespace MathlibPlus.Analysis.Claim47505

/--
The explicit negative cosine alternant in admitted claim 47505.  The two rows
are the frequencies `1` and `2`, and the two columns are the Fourier points
`0` and `1/4`.
-/
theorem cosineAlternant_neg_one_claim47505 :
    let A : Matrix (Fin 2) (Fin 2) ℝ :=
      !![ Real.cos (2 * Real.pi * 0),
          Real.cos (2 * Real.pi * (1 / 4 : ℝ));
          Real.cos (4 * Real.pi * 0),
          Real.cos (4 * Real.pi * (1 / 4 : ℝ)) ]
    Matrix.det A = -1 := by
  dsimp
  have h₁ : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by
    ring
  have h₂ : 4 * Real.pi * (1 / 4 : ℝ) = Real.pi := by
    ring
  rw [h₁, h₂]
  simp [Matrix.det_fin_two]

end MathlibPlus.Analysis.Claim47505
