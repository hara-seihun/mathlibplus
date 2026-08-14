import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffedb7e78

noncomputable def firstShellY (u : ℝ) : ℝ :=
  Real.pi * Real.exp (2 * u)

noncomputable def firstShellQ : ℕ → Polynomial ℝ
  | 0 => 2 * Polynomial.X - Polynomial.C 3
  | n + 1 =>
      (Polynomial.C (5 / 2 : ℝ) - 2 * Polynomial.X) * firstShellQ n +
        2 * Polynomial.X * Polynomial.derivative (firstShellQ n)

noncomputable def firstShell (u : ℝ) : ℝ :=
  2 * Real.rpow Real.pi ((-1 : ℝ) / 4) *
      Real.rpow (firstShellY u) ((5 : ℝ) / 4) *
      Real.exp (-(firstShellY u)) *
      (firstShellQ 0).eval (firstShellY u)

/-- Claim 2953: the first-shell derivative-polynomial recurrence. -/
def claim2953 : Prop :=
  firstShellQ 0 = 2 * Polynomial.X - Polynomial.C 3 ∧
    (∀ n : ℕ,
      firstShellQ (n + 1) =
        (Polynomial.C (5 / 2 : ℝ) - 2 * Polynomial.X) * firstShellQ n +
          2 * Polynomial.X * Polynomial.derivative (firstShellQ n)) ∧
    (∀ (n : ℕ) (u : ℝ),
      iteratedDeriv n firstShell u =
        2 * Real.rpow Real.pi ((-1 : ℝ) / 4) *
          Real.rpow (firstShellY u) ((5 : ℝ) / 4) *
          Real.exp (-(firstShellY u)) *
          (firstShellQ n).eval (firstShellY u))

noncomputable def generalizedBellH : ℕ → Polynomial ℝ
  | 0 => 0
  | 1 => Polynomial.X - Polynomial.C (3 / 2 : ℝ)
  | n + 2 =>
      (Polynomial.X - Polynomial.C (5 / 4 : ℝ)) * generalizedBellH (n + 1) -
        Polynomial.X * Polynomial.derivative (generalizedBellH (n + 1))

/-- Claim 2954: the monic generalized-Bell recurrence. -/
def claim2954 : Prop :=
  generalizedBellH 1 = Polynomial.X - Polynomial.C (3 / 2 : ℝ) ∧
    (∀ m : ℕ, 1 ≤ m →
      generalizedBellH (m + 1) =
        (Polynomial.X - Polynomial.C (5 / 4 : ℝ)) * generalizedBellH m -
          Polynomial.X * Polynomial.derivative (generalizedBellH m)) ∧
    (∀ m : ℕ, 1 ≤ m → (generalizedBellH m).Monic)

def IsSimpleRealRoot (p : Polynomial ℝ) (x : ℝ) : Prop :=
  p.eval x = 0 ∧ (Polynomial.derivative p).eval x ≠ 0

def RootEnumeration (p : Polynomial ℝ) (n : ℕ) (roots : ℕ → ℝ) : Prop :=
  (∀ i : ℕ, i < n → IsSimpleRealRoot p (roots i)) ∧
    (∀ x : ℝ, p.eval x = 0 ↔ ∃ i : ℕ, i < n ∧ x = roots i)

def StrictlyIncreasingOn (roots : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ ⦃i j : ℕ⦄, i < n → j < n → i < j → roots i < roots j

def Interlaces (m : ℕ) (rho sigma : ℕ → ℝ) : Prop :=
  sigma 0 < rho 0 ∧
    (∀ i : ℕ, i + 1 < m →
      rho i < sigma (i + 1) ∧ sigma (i + 1) < rho (i + 1)) ∧
    rho (m - 1) < sigma m

/-- Claim 2957: all-rank positive simple roots and strict interlacing. -/
def claim2957 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∃ rho sigma : ℕ → ℝ,
      RootEnumeration (generalizedBellH m) m rho ∧
        RootEnumeration (generalizedBellH (m + 1)) (m + 1) sigma ∧
        StrictlyIncreasingOn rho m ∧ StrictlyIncreasingOn sigma (m + 1) ∧
        (∀ i : ℕ, i < m → 0 < rho i) ∧
        (∀ i : ℕ, i < m + 1 → 0 < sigma i) ∧
        Interlaces m rho sigma

noncomputable def everyOtherWronskian (r : ℕ) : Polynomial ℝ :=
  Matrix.det (fun i j : Fin r =>
    firstShellQ (2 * (i : ℕ) + (j : ℕ)))

def IntegerWronskianQuotient (r : ℕ) (P : Polynomial ℤ) : Prop :=
  Polynomial.X ^ (r * (r - 1) / 2) *
      Polynomial.map (Int.castRingHom ℝ) P = everyOtherWronskian r

/-- Claim 2959: the exact every-other Wronskian quotient. -/
def claim2959 : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    ∃ P : Polynomial ℤ,
      IntegerWronskianQuotient r P ∧
        P.natDegree = r * (r + 1) / 2

noncomputable def shiftedIntegerPolynomial (P : Polynomial ℤ) (r : ℕ) : Polynomial ℤ :=
  P.comp (Polynomial.X + Polynomial.C (2 * (r : ℤ) - 1))

noncomputable def integerPolynomialEvalReal (P : Polynomial ℤ) (y : ℝ) : ℝ :=
  (Polynomial.map (Int.castRingHom ℝ) P).eval y

/-- Claim 2960: shifted coefficient positivity through rank twenty-three. -/
def claim2960 : Prop :=
  ∀ r : ℕ, 2 ≤ r → r ≤ 23 →
    ∃ P : Polynomial ℤ,
      IntegerWronskianQuotient r P ∧
        (∀ n : ℕ,
          n ≤ (shiftedIntegerPolynomial P r).natDegree →
            0 < (shiftedIntegerPolynomial P r).coeff n) ∧
        (∀ y : ℝ, 2 * (r : ℝ) - 1 ≤ y →
          0 < integerPolynomialEvalReal P y)

def OpenRectangle (a b c d : ℝ) : Set ℂ :=
  {z | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

noncomputable def analyticZeroOrder (f : ℂ → ℂ) (z : ℂ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ,
      iteratedDeriv n f z ≠ 0 ∧
        ∀ k : ℕ, k < n → iteratedDeriv k f z = 0
    then Nat.find h
    else 0

def ZeroCountInRectangle (f : ℂ → ℂ) (R : Set ℂ) (N : ℕ) : Prop :=
  ∃ k : ℕ, ∃ roots : Fin k → ℂ,
    Pairwise (fun i j => roots i ≠ roots j) ∧
      (∀ i : Fin k,
        roots i ∈ R ∧ f (roots i) = 0 ∧
          0 < analyticZeroOrder f (roots i)) ∧
      (∀ z : ℂ, z ∈ R →
        (f z = 0 ↔ ∃ i : Fin k, z = roots i)) ∧
      (∑ i : Fin k, analyticZeroOrder f (roots i) = N)

def RealSignChangeInterval (f : ℂ → ℂ) (left right : ℝ) : Prop :=
  left < right ∧
    (∀ x : ℝ, left ≤ x → x ≤ right → (f (x : ℂ)).im = 0) ∧
    (((f (left : ℂ)).re < 0 ∧ 0 < (f (right : ℂ)).re) ∨
      ((f (right : ℂ)).re < 0 ∧ 0 < (f (left : ℂ)).re))

/-- Claim 2979: winding/sign-count simplicity principle. -/
def claim2979 : Prop :=
  ∀ (f : ℂ → ℂ) (a b c d : ℝ) (N : ℕ),
    a < b → c < d → c < 0 → 0 < d →
      Differentiable ℂ f →
      ZeroCountInRectangle f (OpenRectangle a b c d) N →
      ∀ left right : Fin N → ℝ,
        (∀ i : Fin N,
          RealSignChangeInterval f (left i) (right i) ∧
            a < left i ∧ right i < b) →
        (∀ ⦃i j : Fin N⦄, i ≠ j →
          right i < left j ∨ right j < left i) →
        (∀ z : ℂ, z ∈ OpenRectangle a b c d → f z = 0 →
          z.im = 0 ∧ analyticZeroOrder f z = 1)

end MathlibPlus.Open.ResearchFormalization.Batch019ffedb7e78
