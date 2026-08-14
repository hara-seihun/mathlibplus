import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.BaezDuarte

open scoped BigOperators

/-- The real-valued restriction of the complex Riemann zeta function. -/
def realRiemannZeta (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re

def baezDuarteCoefficient (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    ((-1 : ℝ) ^ j) * (k.choose j : ℝ) /
      realRiemannZeta ((2 * j + 2 : ℕ) : ℝ)

def reciprocalZetaTerm (k : ℕ) (n : ℕ+) : ℝ :=
  (ArithmeticFunction.moebius n.1 : ℝ) / (n.1 : ℝ) ^ 2 *
    (1 - 1 / (n.1 : ℝ) ^ 2) ^ k

def baezDuarteCoefficient_mobius_representation : Prop :=
  ∀ k : ℕ,
    baezDuarteCoefficient k = ∑' n : ℕ+, reciprocalZetaTerm k n ∧
      Summable (fun n : ℕ+ => ‖reciprocalZetaTerm k n‖)

def poissonizedBaezQ (x : ℝ) : ℝ :=
  Real.exp (-x) *
    ∑' k : ℕ, |baezDuarteCoefficient k| ^ 2 * x ^ k / Nat.factorial k

def baezDoubleSumTerm (x : ℝ) (m n : ℕ+) : ℝ :=
  (ArithmeticFunction.moebius m.1 : ℝ) / (m.1 : ℝ) ^ 2 *
    (ArithmeticFunction.moebius n.1 : ℝ) / (n.1 : ℝ) ^ 2 *
    Real.exp (-x *
      (1 / (m.1 : ℝ) ^ 2 + 1 / (n.1 : ℝ) ^ 2 -
        1 / ((m.1 : ℝ) ^ 2 * (n.1 : ℝ) ^ 2)))

def poissonizedBaezQ_double_sum : Prop :=
  ∀ x : ℝ,
    poissonizedBaezQ x =
      ∑' m : ℕ+, ∑' n : ℕ+, baezDoubleSumTerm x m n

def baezPositiveChannel (r : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ+,
    (ArithmeticFunction.moebius n.1 : ℝ) / (n.1 : ℝ) ^ (2 * r + 2) *
      Real.exp (-x / (n.1 : ℝ) ^ 2)

def poissonizedBaezQ_positive_channels : Prop :=
  ∀ x : ℝ,
    poissonizedBaezQ x =
      ∑' r : ℕ, x ^ r * |baezPositiveChannel r x| ^ 2 / Nat.factorial r

def rieszSquare (x : ℝ) : ℝ := x * baezPositiveChannel 0 x

def poissonizedBaezQ_zeroth_channel : Prop :=
  ∀ x : ℝ, 0 < x →
    poissonizedBaezQ x = |rieszSquare x| ^ 2 / x ^ 2 +
      ∑' r : ℕ+, x ^ r.1 * |baezPositiveChannel r.1 x| ^ 2 /
        Nat.factorial r.1 ∧
    ∀ r : ℕ+, 0 ≤ x ^ r.1 * |baezPositiveChannel r.1 x| ^ 2 /
      (Nat.factorial r.1 : ℝ)

def higherPoissonChannels_bound : Prop :=
  (∀ x : ℝ, 1 ≤ x →
    0 ≤ poissonizedBaezQ x - |rieszSquare x| ^ 2 / x ^ 2 ∧
    poissonizedBaezQ x - |rieszSquare x| ^ 2 / x ^ 2 ≤
      x * (∑' n : ℕ+, 1 / (n.1 : ℝ) ^ 4 *
        Real.exp (-x / (2 * (n.1 : ℝ) ^ 2))) ^ 2) ∧
  Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ => poissonizedBaezQ x - |rieszSquare x| ^ 2 / x ^ 2)
    (fun x : ℝ => x ^ (-2 : ℤ))

def lowerIncompleteGamma (a z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..z, t ^ (a - 1) * Real.exp (-t)

def gammaWindowEnergy (N : ℝ) : ℝ :=
  ∫ x in N / 2..4 * N, x ^ (1 / 2 : ℝ) * poissonizedBaezQ x

def gammaWindowEnergy_termwise : Prop :=
  ∀ N : ℝ, 0 < N →
    gammaWindowEnergy N =
      ∑' k : ℕ,
        |baezDuarteCoefficient k| ^ 2 / Nat.factorial k *
          (lowerIncompleteGamma ((k : ℝ) + 3 / 2) (4 * N) -
            lowerIncompleteGamma ((k : ℝ) + 3 / 2) (N / 2))

def rieszLocalEnergy (N : ℝ) : ℝ :=
  ∫ x in N / 2..4 * N, |rieszSquare x| ^ 2 / x ^ (3 / 2 : ℝ)

def gammaWindowEnergy_riesz_asymptotic : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun N : ℝ => gammaWindowEnergy N - rieszLocalEnergy N)
    (fun N : ℝ => N ^ (-1 / 2 : ℝ))

end MathlibPlus.Open.Research.BaezDuarte
