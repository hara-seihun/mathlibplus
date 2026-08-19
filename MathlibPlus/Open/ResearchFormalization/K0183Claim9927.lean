import MathlibPlus.Open.Analysis.ZetaMellinFactorization

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.K0183Claim9927

open MathlibPlus.Open.Analysis

noncomputable section

/-- The arithmetic sum attached to a real source. -/
def arithmeticSum9927 (q : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑' n : ℕ, q (((n + 1 : ℕ) : ℝ) * v)

/-- The logarithmically conjugated arithmetic sum. -/
def bulkKernel9927 (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * arithmeticSum9927 q (Real.exp t)

/-- The even bulk kernel used by the literal Mellin/Fourier transform. -/
def evenBulkKernel9927 (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (bulkKernel9927 q t + bulkKernel9927 q (-t))

/-- The literal transform on the complex spectral axis. -/
noncomputable def literalTransform9927 (L : ℝ) (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in (-L)..L,
    (evenBulkKernel9927 q t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))

/-- The exact grid-flat source carrier at logarithmic scale `L`. -/
def gridFlat9927 (L : ℝ) (q : ℝ → ℝ) : Prop :=
  exactS0Source q ∧
    Function.support q ⊆ Set.Ioo (-Real.exp L) (Real.exp L) ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : ℝ, |v - Real.exp (-L)| < ε → arithmeticSum9927 q v = 0

/-- The central first-order Euler operator. -/
def eulerOperator9927 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * deriv f x + (1 / 2 : ℝ) * f x

/-- The central second-order Euler action `-(x d/dx+1/2)^2`. -/
def centralEulerOperator9927 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -eulerOperator9927 (eulerOperator9927 f) x

/-- Iterates of the central Euler action on a source. -/
def centralEulerIterate9927 : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => centralEulerOperator9927 (centralEulerIterate9927 n f)

/-- The polynomial action `Q(𝒵)q` written as the finite coefficient sum. -/
def centralPolynomialAction9927
    (Q : Polynomial ℝ) (q : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    ∑ n ∈ Q.support,
      Q.coeff n * centralEulerIterate9927 n q x

/-- Iterates of `-∂_t²` on the even bulk kernel. -/
def bulkLaplacianIterate9927 : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, q => evenBulkKernel9927 q
  | n + 1, q =>
      fun t => -deriv (deriv (bulkLaplacianIterate9927 n q)) t

/-- The finite action `Q(-∂_t²)κ_q`. -/
def bulkPolynomialAction9927
    (Q : Polynomial ℝ) (q : ℝ → ℝ) : ℝ → ℝ :=
  fun t =>
    ∑ n ∈ Q.support,
      Q.coeff n * bulkLaplacianIterate9927 n q t

/-- The full bulk Fourier transform. -/
noncomputable def fullBulkTransform9927 (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ,
    (evenBulkKernel9927 q t : ℂ) *
      Complex.exp (Complex.I * z * (t : ℂ))

/-- The multiplier `P_Q(z)=Q(z²)`. -/
def polynomialMultiplier9927 (Q : Polynomial ℝ) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℝ ℂ) (z ^ 2) Q

/-- The canonical full/literal defect split. -/
noncomputable def bulkDefect9927
    (L : ℝ) (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  literalTransform9927 L q z - fullBulkTransform9927 q z

/-- Claim 9927: central polynomial action commutes with the even bulk kernel,
and the resulting full, defect, and literal transforms carry the multiplier
`P_Q(z)=Q(z²)`. -/
def exactCentralPolynomialFactorization_claim9927 : Prop :=
  ∀ (L : ℝ) (q : ℝ → ℝ) (Q : Polynomial ℝ),
    gridFlat9927 L q →
      (∀ t : ℝ,
        evenBulkKernel9927 (centralEulerOperator9927 q) t =
          -deriv (deriv (evenBulkKernel9927 q)) t) ∧
      (∀ t : ℝ,
        evenBulkKernel9927 (centralPolynomialAction9927 Q q) t =
          bulkPolynomialAction9927 Q q t) ∧
      (∀ z : ℂ,
        fullBulkTransform9927 (centralPolynomialAction9927 Q q) z =
          polynomialMultiplier9927 Q z * fullBulkTransform9927 q z) ∧
      (∀ z : ℂ,
        bulkDefect9927 L (centralPolynomialAction9927 Q q) z =
          polynomialMultiplier9927 Q z * bulkDefect9927 L q z) ∧
      (∀ z : ℂ,
        literalTransform9927 L (centralPolynomialAction9927 Q q) z =
          polynomialMultiplier9927 Q z * literalTransform9927 L q z)

end

end MathlibPlus.Open.ResearchFormalization.K0183Claim9927
