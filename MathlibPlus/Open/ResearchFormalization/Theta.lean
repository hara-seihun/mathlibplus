import Mathlib

namespace MathlibPlus.Open.Research.Theta

open scoped BigOperators
noncomputable section

private def thetaShell (t : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * t) -
      3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * t)) *
    Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * t))

def phi (t : ℝ) : ℝ :=
  ∑' n : ℕ, if 1 ≤ n then thetaShell t n else 0

def kernel (t : ℝ) : ℝ := phi |t|

def xShell (t : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * t)

def pInt : ℕ → Polynomial ℤ
  | 0 => Polynomial.X * (2 * Polynomial.X - 3)
  | q + 1 =>
      (1 - 4 * Polynomial.X) * pInt q +
        4 * Polynomial.X * (pInt q).derivative

def pReal (q : ℕ) : Polynomial ℝ :=
  (pInt q).map (Int.castRingHom ℝ)

def theta_shell_derivative_polynomials : Prop :=
  ∀ (q : ℕ) (t : ℝ), 0 ≤ t →
    iteratedDeriv q kernel t =
      Real.exp t *
        (∑' n : ℕ,
          if 1 ≤ n then
            Real.exp (-xShell t n) * (pReal q).eval (xShell t n)
          else 0)

def h1 (t : ℝ) : ℝ := kernel t

def theta_shell_positive (t : ℝ) (n : ℕ) : Prop :=
  0 ≤ t → 1 ≤ n →
    Real.pi ≤ xShell t n ∧
      (3 / 2 : ℝ) < xShell t n ∧ 0 < thetaShell t n

def positivity_of_kernel : Prop :=
  (∀ t : ℝ, ∀ n : ℕ, theta_shell_positive t n) ∧
    ∀ t : ℝ, 0 < h1 t

def first_shell_h2 (x : ℝ) : ℝ := 16 * x ^ 3 * (4 * x ^ 2 - 12 * x + 15)
def first_shell_h3 (x : ℝ) : ℝ :=
  8192 * x ^ 6 * (8 * x ^ 3 - 36 * x ^ 2 + 90 * x - 105)
def first_shell_h4 (x : ℝ) : ℝ :=
  201326592 * x ^ 10 *
    (16 * x ^ 4 - 96 * x ^ 3 + 360 * x ^ 2 - 840 * x + 945)

def orientedFirstShellDet (m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      (pReal ((i : ℕ) + (j : ℕ))).eval x)

def first_shell_confluent_determinants : Prop :=
  ∀ t : ℝ,
    let x := Real.pi * Real.exp (4 * t)
    orientedFirstShellDet 2 x = first_shell_h2 x ∧
      orientedFirstShellDet 3 x = first_shell_h3 x ∧
      orientedFirstShellDet 4 x = first_shell_h4 x

def strictly_increasing_packet (r : ℕ) (x : Fin r → ℝ) : Prop :=
  ∀ ⦃i j : Fin r⦄, i < j → x i < x j

def translation_minor (r : ℕ) (x y : Fin r → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin r => kernel (x i - y j))

def strict_pf_through_four : Prop :=
  ∀ (r : ℕ), 1 ≤ r → r ≤ 4 →
    ∀ (x y : Fin r → ℝ),
      strictly_increasing_packet r x →
      strictly_increasing_packet r y →
      0 < translation_minor r x y

def toeplitz_minor (r : ℕ) (u h : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    kernel (u + (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * h))

def explicit_order_five_witness : Prop :=
  let d5 := toeplitz_minor 5 (1 / 100 : ℝ) (1 / 20 : ℝ)
  let d2 := toeplitz_minor 2 (1 / 100 : ℝ) (1 / 20 : ℝ)
  let d3 := toeplitz_minor 3 (1 / 100 : ℝ) (1 / 20 : ℝ)
  let d4 := toeplitz_minor 4 (1 / 100 : ℝ) (1 / 20 : ℝ)
  (-1847236073442659 : ℝ) / 10 ^ 24 < d5 ∧
    d5 < (-1847236073442658 : ℝ) / 10 ^ 24 ∧
    (3406404062263136923 : ℝ) / 10 ^ 20 < d2 ∧
    (69769706426437948 : ℝ) / 10 ^ 20 < d3 ∧
    (382747136756888845 : ℝ) / 10 ^ 23 < d4

def pf_of_order (r : ℕ) : Prop :=
  ∀ (s : ℕ), s ≤ r →
    ∀ (x y : Fin s → ℝ),
      strictly_increasing_packet s x →
      strictly_increasing_packet s y →
      0 ≤ translation_minor s x y

def exact_polya_frequency_order_four : Prop :=
  strict_pf_through_four ∧ ¬ pf_of_order 5

end
end MathlibPlus.Open.Research.Theta
