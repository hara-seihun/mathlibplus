import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 2609: exact normalized endpoint-wave decomposition. -/
theorem endpointWaveDecomposition_claim2609
    (c t η x : ℝ) (hc : 0 < c) :
    let z : ℂ := (t : ℂ) + (η : ℂ) * Complex.I
    let ell : ℝ := Real.log c / 2
    2 * (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (((t * ell : ℝ) : ℂ) * Complex.I) *
          Complex.cos (z * ((x - ell : ℝ) : ℂ)) =
      (Real.exp (-η * x) : ℂ) *
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) +
        (Real.rpow c (-η) : ℂ) * (Real.exp (η * x) : ℂ) *
          Complex.exp (((-t * x + 2 * t * ell : ℝ) : ℂ) * Complex.I) := by
  dsimp
  calc
    2 * (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (((t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I) *
          Complex.cos (((t : ℂ) + (η : ℂ) * Complex.I) *
            (((x - Real.log c / 2 : ℝ) : ℂ))) =
        (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (((t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I) *
          (2 * Complex.cos (((t : ℂ) + (η : ℂ) * Complex.I) *
            (((x - Real.log c / 2 : ℝ) : ℂ)))) := by ring
    _ = (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (((t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I) *
          (Complex.exp ((((t : ℂ) + (η : ℂ) * Complex.I) *
            (((x - Real.log c / 2 : ℝ) : ℂ)) * Complex.I)) +
           Complex.exp (-(((t : ℂ) + (η : ℂ) * Complex.I) *
            (((x - Real.log c / 2 : ℝ) : ℂ))) * Complex.I)) := by
      rw [Complex.two_cos]
    _ = (Real.exp (-η * x) : ℂ) *
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) +
        (Real.rpow c (-η) : ℂ) * (Real.exp (η * x) : ℂ) *
          Complex.exp (((-t * x + 2 * t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I) := by
      have hhalf : (Real.rpow c (-η / 2) : ℂ) =
          Complex.exp (((Real.log c * (-η / 2) : ℝ) : ℂ)) := by
        exact (congrArg (fun y : ℝ => (y : ℂ))
          (Real.rpow_def_of_pos hc (-η / 2))).trans (Complex.ofReal_exp _)
      have hfull : (Real.rpow c (-η) : ℂ) =
          Complex.exp (((Real.log c * (-η) : ℝ) : ℂ)) := by
        exact (congrArg (fun y : ℝ => (y : ℂ))
          (Real.rpow_def_of_pos hc (-η))).trans (Complex.ofReal_exp _)
      rw [hhalf, hfull, Complex.ofReal_exp, Complex.ofReal_exp]
      have hprod (A B C : ℂ) :
          Complex.exp A * Complex.exp B * Complex.exp C =
            Complex.exp (A + B + C) := by
        calc
          Complex.exp A * Complex.exp B * Complex.exp C =
              Complex.exp (A + B) * Complex.exp C := by rw [← Complex.exp_add]
          _ = Complex.exp ((A + B) + C) := by rw [← Complex.exp_add]
          _ = Complex.exp (A + B + C) := by rfl
      have hplus :
          ((Real.log c * (-η / 2) : ℝ) : ℂ) +
              ((t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I +
              (((t : ℂ) + (η : ℂ) * Complex.I) *
                (((x - Real.log c / 2 : ℝ) : ℂ)) * Complex.I) =
            ((-η * x : ℝ) : ℂ) + ((t * x : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring_nf
        simp only [Complex.I_sq]
        ring
      have hminus :
          ((Real.log c * (-η / 2) : ℝ) : ℂ) +
              ((t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I +
              (-(((t : ℂ) + (η : ℂ) * Complex.I) *
                (((x - Real.log c / 2 : ℝ) : ℂ))) * Complex.I) =
            ((Real.log c * (-η) : ℝ) : ℂ) +
              ((η * x : ℝ) : ℂ) +
              ((-t * x + 2 * t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring_nf
        simp only [Complex.I_sq]
        ring
      rw [mul_add, hprod, hprod, hplus, hminus]
      rw [Complex.exp_add ((-η * x : ℝ) : ℂ) (((t * x : ℝ) : ℂ) * Complex.I)]
      rw [Complex.exp_add
        (((Real.log c * (-η) : ℝ) : ℂ) + ((η * x : ℝ) : ℂ))
        (((-t * x + 2 * t * (Real.log c / 2) : ℝ) : ℂ) * Complex.I)]
      rw [Complex.exp_add ((Real.log c * (-η) : ℝ) : ℂ) ((η * x : ℝ) : ℂ)]

end
end MathlibPlus.Analysis
