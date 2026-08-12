import Mathlib

namespace MathlibPlus.Algebra.Claim13055

/-- The odd-modulus reduction in claim 13055.  The displayed cotangent and
phase carriers are not reconstructed here; this is the exact modular core. -/
theorem balanced_modular_reduction_claim13055 (a n : ℕ) (hn : n = 2 * a + 1) :
    (2 : ZMod n) * (a : ZMod n) = -1 ∧
      (a : ZMod n) * (-2 : ZMod n) = 1 := by
  subst n
  have hzero : ((2 * a + 1 : ℕ) : ZMod (2 * a + 1)) = 0 :=
    ZMod.natCast_self _
  have htwo : ((2 * a : ℕ) : ZMod (2 * a + 1)) = -1 := by
    calc
      ((2 * a : ℕ) : ZMod (2 * a + 1)) =
          ((2 * a + 1 : ℕ) : ZMod (2 * a + 1)) - 1 := by
            push_cast
            ring
      _ = -1 := by rw [hzero]; ring
  constructor
  · calc
      (2 : ZMod (2 * a + 1)) * (a : ZMod (2 * a + 1)) =
          ((2 * a : ℕ) : ZMod (2 * a + 1)) := by
            push_cast
            ring
      _ = -1 := htwo
  · calc
      (a : ZMod (2 * a + 1)) * (-2 : ZMod (2 * a + 1)) =
          -((2 * a : ℕ) : ZMod (2 * a + 1)) := by
            push_cast
            ring
      _ = 1 := by rw [htwo]; ring

end MathlibPlus.Algebra.Claim13055

namespace MathlibPlus.Algebra.Claim50161

/-- The displayed sharp marginal-defect expression is nonnegative for the
natural clone counts and nonnegative slack variables. -/
theorem sharp_marginal_defect_nonneg_claim50161
    (a b M : ℕ) (x y z w : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : 1 ≤ M)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    (a : ℝ) * (2 * (a : ℝ) - 1) * ((M : ℝ) - 1) * x +
        (b : ℝ) * (2 * (b : ℝ) - 1) * ((M : ℝ) - 1) * y +
        2 * (a : ℝ) * (b : ℝ) * ((M : ℝ) - 1) * z +
        (a : ℝ) * (2 * (b : ℝ) - 1) * w ≥ 0 := by
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast (Nat.zero_le a)
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast (Nat.zero_le b)
  have hM0 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h2a : 0 ≤ 2 * (a : ℝ) - 1 := by linarith
  have h2b : 0 ≤ 2 * (b : ℝ) - 1 := by linarith
  have hm : 0 ≤ (M : ℝ) - 1 := by linarith
  have hterm1 : 0 ≤ (a : ℝ) * (2 * (a : ℝ) - 1) * ((M : ℝ) - 1) * x := by positivity
  have hterm2 : 0 ≤ (b : ℝ) * (2 * (b : ℝ) - 1) * ((M : ℝ) - 1) * y := by positivity
  have hterm3 : 0 ≤ 2 * (a : ℝ) * (b : ℝ) * ((M : ℝ) - 1) * z := by positivity
  have hterm4 : 0 ≤ (a : ℝ) * (2 * (b : ℝ) - 1) * w := by positivity
  linarith

end MathlibPlus.Algebra.Claim50161
