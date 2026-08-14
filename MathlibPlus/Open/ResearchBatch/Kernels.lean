import Mathlib

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.ResearchBatch.Kernels

def mobiusLaplaceKernel (N : ℕ) (t : ℝ) : ℝ :=
  ∑' b : ℕ,
    if 0 < b ∧ Nat.Coprime b N then
      (ArithmeticFunction.moebius b : ℝ) * Real.exp (-t * (b : ℝ)) / (b : ℝ)
    else 0

def logarithmicCoprimeKernel (N : ℕ) (t : ℝ) : ℝ :=
  ∑' a : ℕ,
    if 0 < a ∧ Nat.Coprime a N then
      Real.exp (-t * (a : ℝ)) / (a : ℝ)
    else 0

def twoVariableKernel (N : ℕ) (x y : ℝ) : ℝ :=
  ∑' a : ℕ,
    if 0 < a ∧ Nat.Coprime a N then
      Real.exp (-y * (a : ℝ)) * mobiusLaplaceKernel N (x * (a : ℝ)) /
        (a : ℝ)
    else 0

def two_exact_one_dimensional_reductions : Prop :=
  ∀ (N : ℕ) (x y : ℝ), 0 < N → 0 < x → 0 < y →
    (twoVariableKernel N x y =
        (∑' a : ℕ,
          if 0 < a ∧ Nat.Coprime a N then
            Real.exp (-y * (a : ℝ)) * mobiusLaplaceKernel N (x * (a : ℝ)) /
              (a : ℝ)
          else 0)) ∧
    twoVariableKernel N x y =
        (∑' b : ℕ,
          if 0 < b ∧ Nat.Coprime b N then
            (ArithmeticFunction.moebius b : ℝ) *
              logarithmicCoprimeKernel N (y + x * (b : ℝ)) / (b : ℝ)
          else 0)

def finite_divisor_formula_for_logarithmic_kernel : Prop :=
  ∀ (N : ℕ) (t : ℝ), 0 < N → 0 < t →
    logarithmicCoprimeKernel N t =
      -∑ d ∈ N.divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
          Real.log (1 - Real.exp (-t * (d : ℝ)))

def coprime_mobius_laplace_pnt_bound : Prop :=
  ∀ N : ℕ, 0 < N →
    ∃ (cN CN : ℝ), 0 < cN ∧ 0 < CN ∧
      ∀ t : ℝ, 0 < t → t ≤ (1 / 2 : ℝ) →
        |mobiusLaplaceKernel N t| ≤
          CN * Real.exp (-cN * Real.sqrt (Real.log (1 / t)))

def boundaryScalingConstant (N : ℕ) (lam : ℝ) : ℝ :=
  ((Nat.totient N : ℝ) / (N : ℝ)) *
    ∫ r in Set.Ioi (0 : ℝ),
      Real.exp (-r) * mobiusLaplaceKernel N (lam * r) / r

def fixed_modulus_boundary_scaling_theorem : Prop :=
  ∀ (N : ℕ) (lam : ℝ), 0 < N → Squarefree N → 0 < lam →
    Tendsto (fun u : ℝ => twoVariableKernel N (u * lam) u)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (boundaryScalingConstant N lam))

def primeDivisorSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∣ n)

def jordanTotient (k n : ℕ) : ℝ :=
  (n : ℝ) ^ k *
    ∏ p ∈ primeDivisorSet n,
      (1 - Real.rpow (p : ℝ) (-(k : ℝ)))

def jordanRecombinedKernel (N : ℕ) (u x : ℝ) : ℝ :=
  Real.exp (-x) +
    ∑' k : ℕ,
      if 0 < k then
        (-u) ^ k / (Nat.factorial k : ℝ) *
          (∑' n : ℕ,
            if 0 < n ∧ Nat.Coprime n N then
              jordanTotient k n * Real.exp (-x * (n : ℝ)) / (n : ℝ)
            else 0)
      else 0

def exact_jordan_recombination_at_finite_cutoff : Prop :=
  ∀ (N : ℕ) (u : ℝ), 2 ≤ N → 0 < u →
    twoVariableKernel N (u * (N : ℝ)) u =
      jordanRecombinedKernel N u (u * (N : ℝ))

def cutoffKernelQ (N : ℕ) (u : ℝ) : ℝ :=
  u / (1 - Real.exp (-u * (N : ℝ)))

def pointwise_cutoff_uniform_signed_kernel_estimate : Prop :=
  ∀ (N : ℕ) (u : ℝ), 2 ≤ N → 0 < u → u ≤ (1 / 2 : ℝ) →
    cutoffKernelQ N u < 1 ∧
    |twoVariableKernel N (u * (N : ℝ)) u - Real.exp (-u * (N : ℝ))| ≤
      Real.exp (-u * (N : ℝ)) *
        Real.log (1 / (1 - cutoffKernelQ N u))

def uniform_numerical_bound_257 : Prop :=
  ∀ (N : ℕ) (u : ℝ), 2 ≤ N → 0 < u → u ≤ (1 / 2 : ℝ) →
    cutoffKernelQ N u ≤ (1 / 2 : ℝ) / (1 - Real.exp (-1)) ∧
    (1 / 2 : ℝ) / (1 - Real.exp (-1)) < (791 / 1000 : ℝ) ∧
    |twoVariableKernel N (u * (N : ℝ)) u| < (2.57 : ℝ)

end MathlibPlus.Open.ResearchBatch.Kernels
