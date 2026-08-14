import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- A polynomial has nonnegative coefficients in the variables `b` and `m`. -/
def coefficientwisePositive (p : MvPolynomial (Fin 2) ℚ) : Prop :=
  ∀ d, 0 ≤ p.coeff d

local notation "q" => MvPolynomial.C
local notation "b" => (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)
local notation "m" => (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)

/-- The cleared `n = 3` base from Claim 1711. -/
noncomputable def T3 : MvPolynomial (Fin 2) ℚ :=
    64 * b ^ 6
      + (160 * m + 736) * b ^ 5
      + (176 * m ^ 2 + 1600 * m + 3584) * b ^ 4
      + (108 * m ^ 3 + 1468 * m ^ 2 + 6576 * m + 9680) * b ^ 3
      + (q (233 / 6) * m ^ 4 + q (2119 / 3) * m ^ 3
          + q (28639 / 6) * m ^ 2 + q (42581 / 3) * m + 15688) * b ^ 2
      + (q (31 / 4) * m ^ 5 + q (2135 / 12) * m ^ 4
          + q (19433 / 12) * m ^ 3 + q (87745 / 12) * m ^ 2
          + q (98513 / 6) * m + 14732) * b
      + q (97 / 144) * m ^ 6 + q (301 / 16) * m ^ 5
      + q (31219 / 144) * m ^ 4 + q (63485 / 48) * m ^ 3
      + q (162703 / 36) * m ^ 2 + q (98827 / 12) * m + 6280

/-- `T₃(m + 1, b)`, with the two variables retained as `b` and `m`. -/
noncomputable def T3Shift : MvPolynomial (Fin 2) ℚ :=
    64 * b ^ 6
      + (160 * (m + 1) + 736) * b ^ 5
      + (176 * (m + 1) ^ 2 + 1600 * (m + 1) + 3584) * b ^ 4
      + (108 * (m + 1) ^ 3 + 1468 * (m + 1) ^ 2
          + 6576 * (m + 1) + 9680) * b ^ 3
      + (q (233 / 6) * (m + 1) ^ 4 + q (2119 / 3) * (m + 1) ^ 3
          + q (28639 / 6) * (m + 1) ^ 2 + q (42581 / 3) * (m + 1)
          + 15688) * b ^ 2
      + (q (31 / 4) * (m + 1) ^ 5 + q (2135 / 12) * (m + 1) ^ 4
          + q (19433 / 12) * (m + 1) ^ 3 + q (87745 / 12) * (m + 1) ^ 2
          + q (98513 / 6) * (m + 1) + 14732) * b
      + q (97 / 144) * (m + 1) ^ 6 + q (301 / 16) * (m + 1) ^ 5
      + q (31219 / 144) * (m + 1) ^ 4 + q (63485 / 48) * (m + 1) ^ 3
      + q (162703 / 36) * (m + 1) ^ 2 + q (98827 / 12) * (m + 1) + 6280

/-- The `n = 4` instance of the closed form for `Lₙ` from Claim 1710. -/
noncomputable def L4 : MvPolynomial (Fin 2) ℚ :=
  q (1 / 120) * ((m + 8) * (m + 1) * (m + 2)) *
    (40 * (m + 3) * b ^ 3
      + 4 * (11 * m ^ 2 + 84 * m + 165) * b ^ 2
      + (17 * m ^ 3 + 200 * m ^ 2 + 773 * m + 1050) * b
      + q (1 / 6) * ((m + 3) * (m + 6)) * (13 * m ^ 2 + 87 * m + 140))

/-- The explicit exceptional term `E₄` from Claim 1712. -/
noncomputable def E4 : MvPolynomial (Fin 2) ℚ :=
  q (1 / 12) * ((2 * b + m + 6) * (2 * b + m + 7) * (2 * b + m + 8)) *
    (192 * b ^ 4
      + (288 * m + 1440) * b ^ 3
      + (192 * m ^ 2 + 1920 * m + 4704) * b ^ 2
      + (64 * m ^ 3 + 960 * m ^ 2 + 4784 * m + 7968) * b
      + 9 * m ^ 4 + 180 * m ^ 3 + 1359 * m ^ 2 + 4608 * m + 5940)

/-- The `n = 4` recurrence expression for `T₄`. -/
noncomputable def T4 : MvPolynomial (Fin 2) ℚ :=
  (2 * b + m + 8) * T3Shift + L4 + E4

/--
Claim 1712: the exceptional `n = 4` step is coefficientwise positive.
The defining equation for `T4` is exactly
`T₄ = (2b+m+8)T₃(m+1,b) + L₄ + E₄`.
-/
def claim1712 : Prop :=
  coefficientwisePositive T4

end MathlibPlus.Open.ResearchFormalization
