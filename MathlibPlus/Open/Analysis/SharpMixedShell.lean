import Mathlib

noncomputable section

open Filter
open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The polynomial used by the sharp mixed-shell witness. -/
def sharpWitnessE (z : ℂ) : ℂ :=
  (1 + 2 * z) * (1 + z) * (1 + z + z ^ 2) * (1 + (9 : ℂ) * z / 10)

/-- The coefficient sequence of `sharpWitnessE`, extended by zero to negative indices. -/
def sharpWitnessCoeff (n : ℤ) : ℚ :=
  if n = 0 then 1
  else if n = 1 then (49 : ℚ) / 10
  else if n = 2 then (48 : ℚ) / 5
  else if n = 3 then (52 : ℚ) / 5
  else if n = 4 then (13 : ℚ) / 2
  else if n = 5 then (9 : ℚ) / 5
  else 0

/-- The rectangular minors of the coefficient array, with negative coefficients zero. -/
def sharpWitnessD (r k : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin r =>
    sharpWitnessCoeff ((k : ℤ) + (j : ℤ) - (i : ℤ)))

/-- Integer-indexed extension of a nonnegative real coefficient sequence. -/
def extendRealCoefficient (e : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then e n.toNat else 0

/-- The rectangular determinant formed from an integer-indexed coefficient sequence. -/
def determinantFromRealCoefficients (e : ℕ → ℝ) (r k : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    extendRealCoefficient e ((k : ℤ) + (j : ℤ) - (i : ℤ)))

/-- Taylor coefficients at zero, without asserting a global power-series identity. -/
def hasRealTaylorCoefficients (E : ℂ → ℂ) (e : ℕ → ℝ) : Prop :=
  AnalyticAt ℂ E 0 ∧
    ∀ n : ℕ, iteratedDeriv n E 0 = ((Nat.factorial n : ℕ) : ℂ) * (e n : ℂ)

/-- The polynomial whose roots are the inverse lower positive poles. -/
def lowerPolePolynomial (lower : Finset ℝ) (multiplicity : ℝ → ℕ) (X : ℂ) : ℂ :=
  Finset.prod lower (fun a => (X - (a⁻¹ : ℂ)) ^ multiplicity a)

/-- The lower-mode product appearing in the shell scale. -/
def lowerPoleProduct (lower : Finset ℝ) (multiplicity : ℝ → ℕ) : ℝ :=
  Finset.prod lower (fun a => (a⁻¹) ^ multiplicity a)

/-- The pole assertion used below is the norm-to-infinity characterization of a complex pole. -/
def hasComplexPole (f : ℂ → ℂ) (a : ℂ) : Prop :=
  Tendsto (fun z => ‖f z‖) (nhdsWithin a {a}ᶜ) atTop

/-- The exact norm-to-infinity and nonzero-principal-coefficient meaning of a pole order. -/
def hasComplexPoleOrder (f : ℂ → ℂ) (a : ℂ) (m : ℕ) : Prop :=
  hasComplexPole f a ∧
    0 < m ∧
    ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun z => (z - a) ^ m * f z) (nhdsWithin a {a}ᶜ) (nhds c)

/-- The shell contribution in the first residual term. -/
def firstShellContribution (shell : Finset ℂ) (d : ℂ → ℂ)
    (lower : Finset ℝ) (multiplicity : ℝ → ℕ) (n : ℕ) : ℂ :=
  Finset.sum shell (fun β =>
    d β * lowerPolePolynomial lower multiplicity (β⁻¹) ^ 2 *
      Complex.exp (Complex.I * (n : ℂ) * (Complex.arg (β⁻¹) : ℂ)))

/-- The full n-dependent scale outside the parenthesized shell expansion. -/
def firstShellScale (lower : Finset ℝ) (multiplicity : ℝ → ℕ)
    (rho : ℝ) (n : ℕ) : ℂ :=
  (lowerPoleProduct lower multiplicity : ℂ) ^ n * ((rho⁻¹ : ℝ) : ℂ) ^ n

/-- The six rows of the exact periodic formula. -/
def sharpWitnessA : Fin 6 → ℚ := fun s =>
  match s.1 with
  | 0 => (132800 : ℚ) / 3003
  | 1 => (54400 : ℚ) / 1001
  | 2 => (16000 : ℚ) / 273
  | 3 => (4800 : ℚ) / 91
  | 4 => (128000 : ℚ) / 3003
  | 5 => (38400 : ℚ) / 1001
  | _ => 0

def sharpWitnessC : Fin 6 → ℚ := fun s =>
  match s.1 with
  | 0 => (2000 : ℚ) / 273
  | 1 => (300 : ℚ) / 91
  | 2 => (-1000 : ℚ) / 273
  | 3 => (-600 : ℚ) / 91
  | 4 => (-100 : ℚ) / 39
  | 5 => (400 : ℚ) / 91
  | _ => 0

def sharpWitnessF : Fin 6 → ℚ := fun s =>
  match s.1 with
  | 0 => (-17496 : ℚ) / 5005
  | 1 => (-8748 : ℚ) / 5005
  | 2 => (2187 : ℚ) / 910
  | 3 => (2187 : ℚ) / 455
  | 4 => (2187 : ℚ) / 715
  | 5 => (-2187 : ℚ) / 2002
  | _ => 0

def sharpWitnessResidue (n : ℕ) : Fin 6 :=
  ⟨n % 6, Nat.mod_lt _ (by decide)⟩

/-- The poles of the reciprocal of the witness occur in the three asserted modulus shells. -/
def pole_shells_of_sharp_witness_12500 : Prop :=
  (∀ t : ℂ,
      hasComplexPole (fun u => 1 / sharpWitnessE (-u)) t ↔
        t = (1 / 2 : ℂ) ∨
        t = 1 ∨
        t = Complex.exp (Complex.I * (Real.pi / 3)) ∨
        t = Complex.exp (-Complex.I * (Real.pi / 3)) ∨
        t = (10 / 9 : ℂ)) ∧
  ‖(1 / 2 : ℂ)‖ < ‖(1 : ℂ)‖ ∧
  ‖(1 : ℂ)‖ = ‖Complex.exp (Complex.I * (Real.pi / 3))‖ ∧
  ‖(1 : ℂ)‖ = ‖Complex.exp (-Complex.I * (Real.pi / 3))‖ ∧
  ‖(1 : ℂ)‖ < ‖(10 / 9 : ℂ)‖ ∧
  (({(1 : ℂ), Complex.exp (Complex.I * (Real.pi / 3)),
      Complex.exp (-Complex.I * (Real.pi / 3))} : Finset ℂ).Nonempty)

/-- The exact six-periodic boundary-minor formula. -/
def exact_boundary_minor_formula_12501 : Prop :=
  ∀ (r n : ℕ),
    n + 1 = r →
      sharpWitnessD r 2 =
        sharpWitnessA (sharpWitnessResidue n) * (2 : ℚ) ^ n -
          (17496 : ℚ) / 455 * ((9 : ℚ) / 5) ^ n +
          sharpWitnessC (sharpWitnessResidue n) +
          sharpWitnessF (sharpWitnessResidue n) * ((9 : ℚ) / 10) ^ n

/-- The table bounds, exact initial values, and uniform positivity assertion. -/
def uniform_positivity_of_sharp_witness_12502 : Prop :=
  (∀ s : Fin 6,
      sharpWitnessA s ≥ (38400 : ℚ) / 1001 ∧
      |sharpWitnessC s| ≤ (2000 : ℚ) / 273 ∧
      |sharpWitnessF s| ≤ (2187 : ℚ) / 455) ∧
  (∀ n : ℕ, n ≥ 2 →
      sharpWitnessD (n + 1) 2 ≥ (26486917 : ℚ) / 1501500 ∧
      (26486917 : ℚ) / 1501500 > 0) ∧
  sharpWitnessD 1 2 = (48 : ℚ) / 5 ∧
  sharpWitnessD 2 2 = (206 : ℚ) / 5 ∧
  ∀ r : ℕ, r ≥ 1 → sharpWitnessD r 2 > 0

/-- The determinant shell asymptotic with the first-shell hypotheses and its scaled error. -/
def determinant_shell_asymptotic_12496 : Prop :=
  ∀ (E : ℂ → ℂ) (e : ℕ → ℝ) (R rho : ℝ)
    (lower : Finset ℝ) (multiplicity : ℝ → ℕ)
    (shell : Finset ℂ) (d : ℂ → ℂ),
    E 0 = 1 →
    hasRealTaylorCoefficients E e →
    0 < rho → rho < R →
    MeromorphicOn (fun t : ℂ => 1 / E (-t)) (Metric.ball (0 : ℂ) R) →
    (∀ a : ℝ, a ∈ lower → 0 < a ∧ a < rho ∧ 0 < multiplicity a ∧
      hasComplexPoleOrder (fun t : ℂ => 1 / E (-t)) (a : ℂ) (multiplicity a)) →
    shell.Nonempty →
    (∀ beta : ℂ, beta ∈ shell → ‖beta‖ = rho ∧
      hasComplexPoleOrder (fun t : ℂ => 1 / E (-t)) beta 1 ∧
      ¬ ∃ a : ℝ, 0 < a ∧ beta = (a : ℂ)) →
    (∀ beta : ℂ, beta ∈ shell → star beta ∈ shell) →
    (∀ t : ℂ, ‖t‖ ≤ rho →
      (hasComplexPole (fun u : ℂ => 1 / E (-u)) t ↔
        (∃ a : ℝ, a ∈ lower ∧ t = (a : ℂ)) ∨ t ∈ shell)) →
    (∀ beta : ℂ, beta ∈ shell →
      ∃ residue : ℂ,
        Tendsto (fun z => (z - beta) * (1 / E (-z)))
          (nhdsWithin beta {beta}ᶜ) (nhds residue) ∧
        d beta = -residue / beta) →
    let q : ℕ := lower.sum multiplicity
    ∃ (C : ℝ) (lambda : ℝ) (error : ℕ → ℂ),
      C ≠ 0 ∧ 0 < lambda ∧ lambda < 1 ∧
      Asymptotics.IsBigO Filter.atTop error (fun n => (lambda : ℂ) ^ n) ∧
      Filter.Eventually (fun r : ℕ =>
        let n := r - q
        ((determinantFromRealCoefficients e r (q + 1) : ℝ) : ℂ) =
          (C : ℂ) * firstShellScale lower multiplicity rho n *
            (firstShellContribution shell d lower multiplicity n + error n))
        Filter.atTop

end MathlibPlus.Open.Analysis
