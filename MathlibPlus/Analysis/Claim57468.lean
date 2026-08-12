import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim57468

open Polynomial

/-- The fixed Charlier parameter `a = 5/4`. -/
def a : ℚ := (5 : ℚ) / 4

/-- The rational polynomial sequence defined by the admitted recurrence. -/
noncomputable def p : ℕ → Polynomial ℚ :=
  fun n => Nat.rec 1 (fun _ pn =>
    Polynomial.X * pn.derivative +
      (Polynomial.C a - Polynomial.X) * pn) n

/-- The even derivative columns, with the source's domain `j ≥ 1` made
explicit by a subtype. -/
noncomputable def g (j : {j : ℕ // 1 ≤ j}) : Polynomial ℚ :=
  (p (2 * j.1)).derivative

theorem a_value : a = (5 : ℚ) / 4 := by
  rfl

theorem p_zero : p 0 = 1 := by
  rfl

theorem p_succ (n : ℕ) :
    p (n + 1) = Polynomial.X * (p n).derivative +
      (Polynomial.C a - Polynomial.X) * p n := by
  rfl

theorem g_spec (j : {j : ℕ // 1 ≤ j}) :
    g j = (p (2 * j.1)).derivative := by
  rfl

end MathlibPlus.Analysis.Claim57468
