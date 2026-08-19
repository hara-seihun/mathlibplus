import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- The real prime-counting convention used by the C-0069 certificate. -/
noncomputable def primeCountingReal_claim1060 (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Axler's score `A(x) = log x - x / π(x)`. -/
noncomputable def axlerScore_claim1060 (x : ℝ) : ℝ :=
  Real.log x - x / primeCountingReal_claim1060 x

/-- Claim 1060: the exact fixed-point upper certificate and its rational
strict-comparison consequence.  `Z`, `Lᵤ`, and `U` remain integer-valued so
that the final test is an integer inequality. -/
noncomputable def fixedPointLogarithmUpperCertificate_claim1060 : Prop :=
  ∀ (u p z : ℝ),
    0 < u →
    0 < p →
    0 ≤ z →
    z ≤ 10 ^ (-5 : ℤ) →
    z = (p - u) / u →
    let S : ℤ := 2 ^ (56 : ℕ)
    let s : ℝ := (S : ℝ)
    let Z : ℤ := Int.ceil (s * z)
    let Lᵤ : ℤ := Int.ceil (s * Real.log u)
    let U : ℤ :=
      Lᵤ + Z - Int.floor (((Z : ℝ) ^ 2) / (2 * s)) +
        Int.ceil (((Z : ℝ) ^ 3) / (3 * s ^ 2)) -
        Int.floor (p * s / primeCountingReal_claim1060 p)
    axlerScore_claim1060 p ≤ (U : ℝ) / s ∧
      ∀ (a : ℝ) (c d : ℤ),
        0 < d →
        a = (c : ℝ) / (d : ℝ) →
        c * S - d * U > 0 →
          axlerScore_claim1060 p < a

/-- The principal-value logarithmic integral used in the C-0069 source:
`li(x) = lim_{ε → 0+} (∫₀^(1-ε) dt/log t + ∫_(1+ε)^x dt/log t)`. -/
noncomputable def logarithmicIntegral_claim1062 (x : ℝ) : ℝ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun ε : ℝ =>
      (∫ t in (0 : ℝ)..(1 - ε), 1 / Real.log t) +
        (∫ t in (1 + ε)..x, 1 / Real.log t))

/-- The function used in Claim 1062. -/
noncomputable def logarithmicIntegralHandoffFunction_claim1062 (a x : ℝ) : ℝ :=
  x / (Real.log x - a) - logarithmicIntegral_claim1062 x

/-- The exact coefficient/handoff pairs selected in the C-0069 certificate. -/
noncomputable def selectedHandoffs_claim1062 : Fin 42 → ℝ × ℝ :=
  ![
    (1.0344, (98269667551459 : ℝ)),
    (1.0345, (90371487507507 : ℝ)),
    (1.0346, (83148616426618 : ℝ)),
    (1.0347, (76539998116445 : ℝ)),
    (1.0348, (70490385202000 : ℝ)),
    (1.0349, (64949759942696 : ℝ)),
    (1.035, (59872815364303 : ℝ)),
    (1.036, (27203321519991 : ℝ)),
    (1.037, (12902050077142 : ℝ)),
    (1.038, (6366042273460 : ℝ)),
    (1.039, (3257876940837 : ℝ)),
    (1.04, (1724513430371 : ℝ)),
    (1.041, (941875612857 : ℝ)),
    (1.042, (529597645064 : ℝ)),
    (1.043, (305946001836 : ℝ)),
    (1.044, (181255210069 : ℝ)),
    (1.045, (109939829860 : ℝ)),
    (1.046, (68166929664 : ℝ)),
    (1.047, (43145791811 : ℝ)),
    (1.048, (27841451873 : ℝ)),
    (1.049, (18294574359 : ℝ)),
    (1.05, (12228101354 : ℝ)),
    (1.051, (8305548815 : ℝ)),
    (1.052, (5727300390 : ℝ)),
    (1.053, (4006212004 : ℝ)),
    (1.054, (2840388349 : ℝ)),
    (1.055, (2039688286 : ℝ)),
    (1.056, (1482509039 : ℝ)),
    (1.057, (1089944229 : ℝ)),
    (1.058, (810082808 : ℝ)),
    (1.059, (608323943 : ℝ)),
    (1.06, (461316256 : ℝ)),
    (1.061, (353112828 : ℝ)),
    (1.062, (272699918 : ℝ)),
    (1.063, (212388725 : ℝ)),
    (1.064, (166756324 : ℝ)),
    (1.065, (131940295 : ℝ)),
    (1.066, (105163824 : ℝ)),
    (1.067, (84412633 : ℝ)),
    (1.068, (68213019 : ℝ)),
    (1.069, (55477903 : ℝ)),
    (1.07, (45399074 : ℝ))]

/-- Claim 1062: the logarithmic-integral derivative identity and strict
monotonicity, followed by the exact sign and tail derivative conditions at
all selected handoffs. -/
noncomputable def logarithmicIntegralHandoffMonotonicity_claim1062 : Prop :=
  (∀ (a x : ℝ),
      1 < x →
      Real.log x - a ≠ 0 →
        Real.log x * (Real.log x - a) ^ 2 *
            deriv (logarithmicIntegralHandoffFunction_claim1062 a) x =
          (a - 1) * Real.log x - a ^ 2) ∧
    (∀ a : ℝ,
      StrictMonoOn (logarithmicIntegralHandoffFunction_claim1062 a)
        {x : ℝ |
          1 < x ∧
            Real.log x - a ≠ 0 ∧
            (a - 1) * Real.log x > a ^ 2}) ∧
    (∀ i : Fin 42,
      let a : ℝ := (selectedHandoffs_claim1062 i).1
      let T : ℝ := (selectedHandoffs_claim1062 i).2
      logarithmicIntegralHandoffFunction_claim1062 a (T - 1) < 0 ∧
        0 < logarithmicIntegralHandoffFunction_claim1062 a T ∧
        ∀ x : ℝ, T ≤ x →
          (a - 1) * Real.log x > a ^ 2)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
