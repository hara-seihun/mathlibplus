import Mathlib

noncomputable section
open scoped BigOperators Topology
open Filter

namespace MathlibPlus.Open.ResearchFormalization.AnalysisClaims

private def gaussianExponent (N X : ℝ) : ℝ :=
  (3 / 2) * N - Real.pi * X ^ 2

private def gaussianShell (N X : ℝ) (k : ℕ) : ℝ :=
  Real.exp (gaussianExponent N (X + k))

private def primeTowerTerm (p : ℕ) (t : ℝ) (k : ℕ) : ℂ :=
  if 0 < k then
    (Real.log (p : ℝ) : ℂ) /
        (Real.rpow (p : ℝ) ((k : ℝ) / 2)) *
      Complex.exp (-Complex.I * (k : ℂ) * (t : ℂ) * (Real.log (p : ℝ) : ℂ))
  else 0

private def primeTower (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, primeTowerTerm p t k

private def primeTowerSum (P : Finset ℕ) (t : ℝ) : ℂ :=
  Finset.sum P (fun p => primeTower p t)

/-- The recurrence and closed form for the rank multiplicities. -/
def r59446_joint_square_shift_recurrence_closure : Prop :=
  ∀ m : ℕ → ℚ,
    m 2 = 1 / 2 ∧
      (∀ r : ℕ, 3 ≤ r →
        m r = (2 : ℚ) * (Nat.factorial (r - 1) : ℚ) * m (r - 1)) →
      (∀ n : ℕ,
        m (n + 3) =
          (2 : ℚ) ^ n *
            Finset.prod (Finset.range (n + 1))
              (fun j => (Nat.factorial (j + 2) : ℚ))) ∧
      (∀ r : ℕ, 3 ≤ r →
        m r = (2 : ℚ) ^ ((r : ℤ) - 3) *
          Finset.prod (Finset.Icc 2 (r - 1))
            (fun k => (Nat.factorial k : ℚ))) ∧
      m 2 = (2 : ℚ) ^ ((2 : ℤ) - 3) *
        Finset.prod (Finset.Icc 2 (2 - 1))
          (fun k => (Nat.factorial k : ℚ)) ∧
      (m 2 = (1 / 2 : ℚ) ∧ m 3 = 2 ∧ m 4 = 24 ∧
        m 5 = 1152 ∧ m 6 = 276480 ∧ m 7 = 398131200) ∧
      (Nat.factorial (2 - 2) = 1 ∧ Nat.factorial (3 - 2) = 1 ∧
        Nat.factorial (4 - 2) = 2 ∧ Nat.factorial (5 - 2) = 6 ∧
        Nat.factorial (6 - 2) = 24 ∧ Nat.factorial (7 - 2) = 120)

private def everywhereDifferentiable (f : ℝ → ℝ) : Prop :=
  ∀ x, DifferentiableAt ℝ f x

private def derivativeData (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv f x

private def anchoredDerivativeData (f : ℝ → ℝ) : (ℝ → ℝ) × ℝ :=
  (derivativeData f, f 0)

/-- Complete derivative data needs one anchor value for injectivity. -/
def r59450_anchored_derivative_reconstruction_injectivity : Prop :=
  let zero : ℝ → ℝ := fun _ => 0
  let one : ℝ → ℝ := fun _ => 1
  derivativeData zero = derivativeData one ∧ zero ≠ one ∧
    ∀ f g : ℝ → ℝ,
      everywhereDifferentiable f → everywhereDifferentiable g →
      anchoredDerivativeData f = anchoredDerivativeData g → f = g

/-- Finite prime towers return simultaneously to coherent phase. -/
def r59451_finite_prime_tower_rephasing : Prop :=
  ∀ (P : Finset ℕ), P.Nonempty → (∀ p ∈ P, p.Prime) →
    (∀ p ∈ P, ∀ t : ℝ,
      Summable (fun k : ℕ => ‖primeTowerTerm p t k‖)) ∧
    ∃ q : ℕ → ℕ,
      (∀ r, 0 < q r) ∧ Tendsto q atTop atTop ∧
      (∀ p ∈ P,
        Tendsto
          (fun r => Complex.exp
            (Complex.I * (q r : ℂ) * (Real.log (p : ℝ) : ℂ)))
          atTop (𝓝 1)) ∧
      Tendsto (fun r => primeTowerSum P (q r)) atTop
        (𝓝 (Finset.sum P
          (fun p => (Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1) : ℂ)))) ∧
      Filter.limsup (fun t : ℝ => ‖primeTowerSum P t‖) atTop =
        Finset.sum P (fun p => Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1)) ∧
      0 < Finset.sum P (fun p => Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1))

/-- Uniform Gaussian threshold normalization. -/
def r59452_uniform_ge_sqrt_pi_threshold_bound : Prop :=
  ∀ (R : ℝ → ℝ → ℝ) (C α β : ℝ), C ≥ 0 →
    (∀ (N m : ℝ), N ≥ 1 →
      m ^ 2 ≥ (3 / (2 * Real.pi)) * N + α * Real.sqrt N →
      |R N m| ≤ C * Real.rpow N β *
        Real.exp ((3 / 2) * N - Real.pi * m ^ 2)) →
    let A := max 0 (max α β)
    ∀ (N m : ℝ), N ≥ 1 →
      m ^ 2 ≥ (3 / (2 * Real.pi)) * N + A * Real.sqrt N →
      |R N m| ≤ C * Real.rpow N A *
        Real.exp ((3 / 2) * N - Real.pi * m ^ 2) ∧
      C * Real.rpow N A *
          Real.exp ((3 / 2) * N - Real.pi * m ^ 2) ≤
        C * Real.rpow N A * Real.exp (-Real.pi * A * Real.sqrt N)

/-- The first-ratio Gaussian tail bound. -/
def r59590_sharp_first_ratio_gaussian_tail : Prop :=
  ∀ (b : ℕ → ℝ) (B : ℝ) (M : ℕ), B ≥ 0 →
    (∀ k : ℕ, |b k| ≤ B * Real.exp (-Real.pi * (M + k : ℝ) ^ 2)) →
    Summable (fun k => |b k|) ∧
      (∑' k : ℕ, |b k|) ≤
        B * Real.exp (-Real.pi * (M : ℝ) ^ 2) /
          (1 - Real.exp (-Real.pi * (2 * M + 1 : ℝ)))

private def omega (re im : I → ℝ) (m : I → ℤ) (T : ℝ) (i : I) : ℤ :=
  if (1 / 2 : ℝ) < re i ∧ |im i| < T then m i else 0

/-- Cofinal truncation vanishes at every height exactly on the critical line. -/
def r59591_awdt_cofinal_wall_obstruction_detection : Prop :=
  ∀ (I A : Type) (re im : I → ℝ) (m : I → ℤ)
    (partner : I → I) (height : A → ℝ),
    (∀ i, m i ≠ 0) →
    (∀ i, re (partner i) = 1 - re i) →
    (∀ x : ℝ, ∃ a : A, x < height a) →
    ((∀ a : A, ∀ i : I, omega re im m (height a) i = 0) ↔
      ∀ i : I, re i = 1 / 2)

/-- Without constraints, a prescribed endpoint trace extends to an arbitrary family. -/
def r59593_canonical_cone_arbitrary_endpoint_trace : Prop :=
  ∀ (Q : Type) (q : Q) (s : ℕ → ℝ),
    ∃ H : ℕ → Q → ℝ, ∀ N : ℕ, H N q = s N

/-- The omitted Gaussian shells satisfy the geometric first-ratio bound. -/
def r59596_gaussian_omitted_shell_tail : Prop :=
  ∀ (N X : ℝ), X ≥ 0 →
    (∑' k : ℕ, gaussianShell N X k) ≤
      Real.exp (gaussianExponent N X) /
        (1 - Real.exp (-Real.pi * (2 * X + 1)))

end MathlibPlus.Open.ResearchFormalization.AnalysisClaims
