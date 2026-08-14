import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The finite-support Poisson–Charlier polynomial family used by the claims. -/
def poissonCharlierPolynomial (n r : ℕ) : Polynomial ℝ :=
  Nat.rec (Polynomial.monomial n (1 / (n.factorial : ℝ)))
    (fun _ p => p.derivative - p) r

/-- The finite channel polynomial obtained from a finite-place Li sequence. -/
def finiteChannelPolynomial (support : Finset ℕ) (sequence : ℕ → ℝ) (r : ℕ) : Polynomial ℝ :=
  ∑ n ∈ support, sequence n • poissonCharlierPolynomial n r

/-- The real finite channel `F_r(x) = exp(-x) C_r(x)`. -/
def finiteChannel
    (support : Finset ℕ) (sequence : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * (finiteChannelPolynomial support sequence r).eval x

/-- Repeated ordinary derivatives, including the total derivative operator on functions. -/
def iteratedDerivative (r : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  ((fun g : ℝ → ℝ => fun x => deriv g x)^[r]) f

/--
Claim 4463: finite channels are successive derivatives, and the channel of
index `r` is the `r`-fold derivative of channel zero.
-/
def claim4463_channels_successive_derivatives : Prop :=
  (∀ (support : Finset ℕ) (sequence : ℕ → ℝ) (r : ℕ) (x : ℝ),
    HasDerivAt
      (finiteChannel support sequence r)
      (finiteChannel support sequence (r + 1) x) x)
  ∧ (∀ (support : Finset ℕ) (sequence : ℕ → ℝ) (r : ℕ),
      (fun x => finiteChannel support sequence r x) =
        iteratedDerivative r (finiteChannel support sequence 0))

/-- The finite square energy through channel `N - 1`. -/
def finiteSquareEnergy
    (support : Finset ℕ) (sequence : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range N,
    x ^ r * (finiteChannel support sequence r x) ^ 2 / (r.factorial : ℝ)

/--
Claim 4465: in the real finite model the absolute-square expression for the
finite energy is the ordinary-square expression, with the stated cutoff.
-/
def claim4465_finite_square_energy : Prop :=
  ∀ (support : Finset ℕ) (sequence : ℕ → ℝ) (N : ℕ) (x : ℝ),
    finiteSquareEnergy support sequence N x =
      ∑ r ∈ Finset.range N,
        x ^ r * |finiteChannel support sequence r x| ^ 2 /
          (r.factorial : ℝ)

/-- The phase `u_x`, extended by zero at the exceptional arithmetic input 0. -/
def phase (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else Complex.exp (Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ))

/-- The positive product-shell convolution of the two unit phases. -/
def tau (x : ℝ) (k : ℕ) : ℂ :=
  if h : 0 < k then
    ∑ n ∈ (Finset.Icc 1 k).filter (fun n => n ∣ k),
      phase (-x) n * phase x (k / n)
  else 0

/--
Claim 4480: the product-shell coefficient `τ_x` is multiplicative and has
its stated zero and one normalizations.
-/
def claim4480_tau_multiplicative : Prop :=
  ∀ (x : ℝ),
    (∀ (m n : ℕ), Nat.Coprime m n →
      tau x (m * n) = tau x m * tau x n)
    ∧ tau x 0 = 0
    ∧ tau x 1 = 1

end MathlibPlus.Open.ResearchFormalizationBatch
