import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The closed rectangle with real-coordinate sides `a`, `b` and
imaginary-coordinate sides `c`, `d`. -/
def rectangle (a b c d : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

/-- The four positively oriented affine edges of `rectangle`. -/
def lowerEdge (a b c : ℝ) (s : ℝ) : ℂ :=
  Complex.ofReal (a + (b - a) * s) + Complex.I * Complex.ofReal c

def rightEdge (b c d : ℝ) (s : ℝ) : ℂ :=
  Complex.ofReal b + Complex.I * Complex.ofReal (c + (d - c) * s)

def upperEdge (a b d : ℝ) (s : ℝ) : ℂ :=
  Complex.ofReal (b - (b - a) * s) + Complex.I * Complex.ofReal d

def leftEdge (a c d : ℝ) (s : ℝ) : ℂ :=
  Complex.ofReal a + Complex.I * Complex.ofReal (d - (d - c) * s)

/-- The logarithmic-derivative contour expression for the boundary winding
number about zero. -/
noncomputable def rectangleWinding (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ *
    ((∫ s in (0 : ℝ)..1,
        (deriv f (lowerEdge a b c s) / f (lowerEdge a b c s)) *
          Complex.ofReal (b - a)) +
      (∫ s in (0 : ℝ)..1,
        (deriv f (rightEdge b c d s) / f (rightEdge b c d s)) *
          (Complex.I * Complex.ofReal (d - c))) +
      (∫ s in (0 : ℝ)..1,
        (deriv f (upperEdge a b d s) / f (upperEdge a b d s)) *
          (-Complex.ofReal (b - a))) +
      (∫ s in (0 : ℝ)..1,
        (deriv f (leftEdge a c d s) / f (leftEdge a c d s)) *
          (-Complex.I * Complex.ofReal (d - c))))

/-- Claim 1664: the argument-principle rectangle criterion and the integer
rounding consequence of a sufficiently narrow interval enclosure. -/
def claim_1664_argument_principle_rectangle : Prop :=
  (∀ (a b c d : ℝ) (f : ℂ → ℂ),
    a < b →
    c < d →
    AnalyticOnNhd ℂ f (rectangle a b c d) →
    (∀ z ∈ frontier (rectangle a b c d), f z ≠ 0) →
    rectangleWinding f a b c d = 0 →
    ∀ z ∈ rectangle a b c d, f z ≠ 0) ∧
  (∀ (lo hi w : ℝ) (n : ℤ),
    lo ≤ 0 →
    0 ≤ hi →
    -(1 / 4 : ℝ) < lo →
    hi < (1 / 4 : ℝ) →
    lo ≤ w →
    w ≤ hi →
    w = (n : ℝ) →
    n = 0)

end MathlibPlus.Open.ResearchFormalizationBatch
