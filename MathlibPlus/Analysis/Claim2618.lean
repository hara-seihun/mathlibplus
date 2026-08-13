import Mathlib

namespace MathlibPlus.Analysis.Claim2618

noncomputable section

/-- The phase-normalized two-wave decomposition from claim 2618.  The real-power
convention is `Real.rpow`, and all real exponentials are cast into `ℂ`. -/
theorem phaseNormalizedWaveDecomposition
    {c t η x : ℝ} (hc : 0 < c) :
    let L : ℝ := Real.log c
    let ell : ℝ := L / 2
    let z : ℂ := (t : ℂ) + (η : ℂ) * Complex.I
    2 * (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * (ell : ℂ)) *
          Complex.cos (z * ((x - ell : ℝ) : ℂ)) =
      (Real.exp (-η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) +
        (Real.rpow c (-η) : ℂ) * (Real.exp (η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((2 * ell - x : ℝ) : ℂ)) := by
  dsimp
  have hpow (a : ℝ) :
      (Real.rpow c a : ℂ) = Complex.exp ((Real.log c * a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    congr 1
    exact Real.rpow_def_of_pos hc a
  have hmul (a b : ℝ) :
      ((a : ℂ) + (b : ℂ) * Complex.I) * Complex.I =
        (-(b : ℂ)) + (a : ℂ) * Complex.I := by
    calc
      ((a : ℂ) + (b : ℂ) * Complex.I) * Complex.I =
          (a : ℂ) * Complex.I + (b : ℂ) * (Complex.I * Complex.I) := by ring
      _ = (-(b : ℂ)) + (a : ℂ) * Complex.I := by
        rw [Complex.I_mul_I]
        ring
  have hzmul (d : ℝ) :
      ((t : ℂ) + (η : ℂ) * Complex.I) * (d : ℂ) * Complex.I =
        (-(η * d : ℝ) : ℂ) + (t * d : ℝ) * Complex.I := by
    calc
      ((t : ℂ) + (η : ℂ) * Complex.I) * (d : ℂ) * Complex.I =
          (((t * d : ℝ) : ℂ) + ((η * d : ℝ) : ℂ) * Complex.I) * Complex.I := by
            push_cast
            ring
      _ = (-(η * d : ℝ) : ℂ) + (t * d : ℝ) * Complex.I := by
        exact hmul (t * d) (η * d)
  have hplusExp :
      ((Real.log c * (-η / 2) : ℝ) : ℂ) +
          Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ) +
          ((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I =
        ((-η * x : ℝ) : ℂ) + Complex.I * (t : ℂ) * (x : ℂ) := by
    rw [hzmul]
    push_cast
    ring
  have hminusExp :
      ((Real.log c * (-η / 2) : ℝ) : ℂ) +
          Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ) -
          (((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I) =
        ((Real.log c * (-η) : ℝ) : ℂ) + (η * x : ℝ) +
          Complex.I * (t : ℂ) * ((Real.log c - x : ℝ) : ℂ) := by
    rw [hzmul]
    push_cast
    ring
  have hexp3 (a b d : ℂ) :
      Complex.exp a * Complex.exp b * Complex.exp d =
        Complex.exp (a + b + d) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
  have hplus :
      (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) *
          Complex.exp (((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I) =
        (Real.exp (-η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
    rw [hpow (-η / 2)]
    calc
      Complex.exp ((Real.log c * (-η / 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) *
          Complex.exp (((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((Real.log c * (-η / 2) : ℝ) : ℂ) +
            Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ) +
            ((t : ℂ) + (η : ℂ) * Complex.I) *
              ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I) := by
                exact hexp3 _ _ _
      _ = Complex.exp (((-η * x : ℝ) : ℂ) +
            Complex.I * (t : ℂ) * (x : ℂ)) := by rw [hplusExp]
      _ = (Real.exp (-η * x) : ℂ) *
            Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
                rw [Complex.exp_add, ← Complex.ofReal_exp]
  have hminus :
      (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) *
          Complex.exp (-(((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I)) =
        (Real.rpow c (-η) : ℂ) * (Real.exp (η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) *
            ((Real.log c - x : ℝ) : ℂ)) := by
    rw [hpow (-η / 2), hpow (-η)]
    calc
      Complex.exp ((Real.log c * (-η / 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) *
          Complex.exp (-(((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (((Real.log c * (-η / 2) : ℝ) : ℂ) +
            Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ) -
            (((t : ℂ) + (η : ℂ) * Complex.I) *
              ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I)) := by
                exact hexp3 _ _ _
      _ = Complex.exp (((Real.log c * (-η) : ℝ) : ℂ) +
            (η * x : ℝ) +
            Complex.I * (t : ℂ) * ((Real.log c - x : ℝ) : ℂ)) := by
                rw [hminusExp]
      _ = Complex.exp ((Real.log c * (-η) : ℝ) : ℂ) *
            (Real.exp (η * x) : ℂ) *
            Complex.exp (Complex.I * (t : ℂ) *
              ((Real.log c - x : ℝ) : ℂ)) := by
                rw [Complex.exp_add, Complex.exp_add, Complex.ofReal_exp]
  rw [Complex.cos]
  have hneg :
      -(((t : ℂ) + (η : ℂ) * Complex.I) *
          ((x - Real.log c / 2 : ℝ) : ℂ)) * Complex.I =
        -(((t : ℂ) + (η : ℂ) * Complex.I) *
          ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I) := by ring
  rw [hneg]
  calc
    2 * (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) *
          ((Complex.exp (((t : ℂ) + (η : ℂ) * Complex.I) *
              ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I) +
            Complex.exp (-(((t : ℂ) + (η : ℂ) * Complex.I) *
              ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I))) / 2) =
        (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) *
          Complex.exp (((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I) +
        (Real.rpow c (-η / 2) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) *
          Complex.exp (-(((t : ℂ) + (η : ℂ) * Complex.I) *
            ((x - Real.log c / 2 : ℝ) : ℂ) * Complex.I)) := by ring
    _ = (Real.exp (-η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) +
        (Real.rpow c (-η) : ℂ) * (Real.exp (η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) *
            ((Real.log c - x : ℝ) : ℂ)) := by rw [hplus, hminus]
    _ = (Real.exp (-η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) +
        (Real.rpow c (-η) : ℂ) * (Real.exp (η * x) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) *
            ((2 * (Real.log c / 2) - x : ℝ) : ℂ)) := by
      congr 1
      rw [show (2 * (Real.log c / 2 : ℝ) - x : ℝ) = Real.log c - x by ring]

end
end MathlibPlus.Analysis.Claim2618
