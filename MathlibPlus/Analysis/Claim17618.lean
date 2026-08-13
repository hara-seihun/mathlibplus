import Mathlib

namespace MathlibPlus.Analysis.Claim17618

/-- Common-divisor transport for the explicit Gaussian shell from claim 17618. -/
theorem commonDivisorTransport_claim17618
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (w : ℝ) :
    let g : ℕ → ℝ → ℝ := fun k t =>
      Real.exp (t / 2) *
        Real.exp (-Real.pi * (k : ℝ) ^ 2 * Real.exp (2 * t))
    ((d : ℝ) * (n : ℝ)) ^ (-1 / 2 : ℝ) * g 1 (w + Real.log d) =
      (n : ℝ) ^ (-1 / 2 : ℝ) * g d w := by
  dsimp
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : Real.exp (Real.log (d : ℝ) / 2) =
      (d : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hdR]
    congr 1
    ring
  have htwo : Real.exp (2 * (w + Real.log (d : ℝ))) =
      Real.exp (2 * w) * (d : ℝ) ^ 2 := by
    rw [show 2 * (w + Real.log (d : ℝ)) =
      2 * w + (2 : ℝ) * Real.log (d : ℝ) by ring,
      Real.exp_add]
    rw [show (2 : ℝ) * Real.log (d : ℝ) =
      Real.log (d : ℝ) + Real.log (d : ℝ) by ring,
      Real.exp_add, Real.exp_log hdR]
    ring
  have hfirst : Real.exp ((w + Real.log (d : ℝ)) / 2) =
      Real.exp (w / 2) * (d : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (w + Real.log (d : ℝ)) / 2 =
      w / 2 + Real.log (d : ℝ) / 2 by ring,
      Real.exp_add, hhalf]
  have hsplit : ((d : ℝ) * (n : ℝ)) ^ (-1 / 2 : ℝ) =
      (d : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) := by
    exact Real.mul_rpow (le_of_lt hdR) (le_of_lt hnR)
  rw [hsplit, hfirst, htwo]
  norm_num only [Nat.cast_one, one_pow, one_mul, mul_one]
  have harg : -Real.pi * (Real.exp (2 * w) * (d : ℝ) ^ 2) =
      -Real.pi * (d : ℝ) ^ 2 * Real.exp (2 * w) := by ring
  rw [harg]
  have hcancel' : (d : ℝ) ^ (-(1 / 2 : ℝ)) *
      (d : ℝ) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hdR]
    norm_num
  calc
    (d : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (w / 2) * (d : ℝ) ^ (1 / 2 : ℝ) *
            Real.exp (-Real.pi * (d : ℝ) ^ 2 * Real.exp (2 * w))) =
        ((d : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (1 / 2 : ℝ)) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
            (Real.exp (w / 2) *
              Real.exp (-Real.pi * (d : ℝ) ^ 2 * Real.exp (2 * w)))) := by ring
    _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (w / 2) *
            Real.exp (-Real.pi * (d : ℝ) ^ 2 * Real.exp (2 * w))) := by
      rw [hcancel']
      ring

end MathlibPlus.Analysis.Claim17618
