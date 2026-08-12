import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim20741

/-- The fixed six margins determine every other cell from `t = x₁₂₃`. -/
theorem fixed_six_margins_parameterization_claim20741
    (q C12 C13 C23 D1 D2 D3 t x123 x12 x13 x23 x1 x2 x3 x0 : ℤ)
    (ht : t = x123)
    (h12 : x12 + x123 = C12)
    (h13 : x13 + x123 = C13)
    (h23 : x23 + x123 = C23)
    (h1 : x1 + x12 + x13 + x123 = D1)
    (h2 : x2 + x12 + x23 + x123 = D2)
    (h3 : x3 + x13 + x23 + x123 = D3)
    (hTotal : x0 + x1 + x2 + x3 + x12 + x13 + x23 + x123 = q) :
    x12 = C12 - t ∧
      x13 = C13 - t ∧
      x23 = C23 - t ∧
      x1 = D1 - C12 - C13 + t ∧
      x2 = D2 - C12 - C23 + t ∧
      x3 = D3 - C13 - C23 + t ∧
      x0 = q - D1 - D2 - D3 + C12 + C13 + C23 - t := by
  omega

/-- Nonnegative tables with fixed margins form an integer interval in their
free coordinate. -/
theorem fixed_six_margins_feasible_interval_claim20741
    (q C12 C13 C23 D1 D2 D3 lo hi u : ℤ)
    (hlo :
      0 ≤ lo ∧ 0 ≤ C12 - lo ∧ 0 ≤ C13 - lo ∧ 0 ≤ C23 - lo ∧
      0 ≤ D1 - C12 - C13 + lo ∧
      0 ≤ D2 - C12 - C23 + lo ∧
      0 ≤ D3 - C13 - C23 + lo ∧
      0 ≤ q - D1 - D2 - D3 + C12 + C13 + C23 - lo)
    (hhi :
      0 ≤ hi ∧ 0 ≤ C12 - hi ∧ 0 ≤ C13 - hi ∧ 0 ≤ C23 - hi ∧
      0 ≤ D1 - C12 - C13 + hi ∧
      0 ≤ D2 - C12 - C23 + hi ∧
      0 ≤ D3 - C13 - C23 + hi ∧
      0 ≤ q - D1 - D2 - D3 + C12 + C13 + C23 - hi)
    (hlo_u : lo ≤ u) (hu_hi : u ≤ hi) :
    0 ≤ u ∧ 0 ≤ C12 - u ∧ 0 ≤ C13 - u ∧ 0 ≤ C23 - u ∧
      0 ≤ D1 - C12 - C13 + u ∧
      0 ≤ D2 - C12 - C23 + u ∧
      0 ≤ D3 - C13 - C23 + u ∧
      0 ≤ q - D1 - D2 - D3 + C12 + C13 + C23 - u := by
  omega

end MathlibPlus.Algebra.Claim20741
