import Mathlib

namespace MathlibPlus.Analysis.ThetaShellTranslation

/-- The exact translation law from admitted claim 15231, with the displayed
negative half-power represented by `Real.rpow` and identified with its
exponential/logarithmic form in the proof. -/
theorem thetaShellTranslation (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (u : ℝ) :
    let x (k : ℕ) (v : ℝ) := Real.pi * (k : ℝ) ^ 2 * Real.exp (2 * v)
    let φ (k : ℕ) (v : ℝ) :=
      Real.exp (v / 2) * (4 * x k v ^ 2 - 6 * x k v) * Real.exp (-x k v)
    φ (d * n) u =
      (d : ℝ) ^ (-1 / 2 : ℝ) * φ n (u + Real.log (d : ℝ)) := by
  dsimp
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlog : Real.exp (2 * Real.log (d : ℝ)) = (d : ℝ) ^ 2 := by
    simpa [Real.exp_log hdR] using (Real.exp_nat_mul (Real.log (d : ℝ)) 2)
  have hx :
      Real.pi * ((d * n : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) =
        Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * (u + Real.log (d : ℝ))) := by
    rw [Nat.cast_mul]
    rw [show (2 : ℝ) * (u + Real.log (d : ℝ)) =
      2 * u + 2 * Real.log (d : ℝ) by ring, Real.exp_add, hlog]
    ring
  have hpow :
      (d : ℝ) ^ (-1 / 2 : ℝ) = Real.exp (-Real.log (d : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hdR]
    congr 1
    ring
  have hpref :
      Real.exp (u / 2) =
        Real.exp (-Real.log (d : ℝ) / 2) *
          Real.exp ((u + Real.log (d : ℝ)) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpow, hx, hpref]
  ring

end MathlibPlus.Analysis.ThetaShellTranslation
