import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section
open Classical
open scoped BigOperators

/-- The source-channel transform from the admitted logarithmic-derivative formula. -/
def sourceChannelTransform (R : ℝ → ℝ) (lam mu : ℝ) : ℝ :=
  4 * (mu * R lam - lam * R mu) / (mu ^ 2 - lam ^ 2)

/-- The all-entry resolvent kernel, with the removable diagonal value retained. -/
def resolventChannelKernel (b lam mu : ℝ) : ℝ :=
  if lam = mu then
    4 * (lam + mu + b) / ((lam + b) * (mu + b) * (lam + mu))
  else
    sourceChannelTransform (fun x : ℝ => 1 / (x + b)) lam mu

/-- The Cauchy matrix carried by a finite list of nodes. -/
def cauchyMatrix {N : ℕ} (nodes : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => 1 / (nodes i + nodes j)

/-- The matrix of all ones. -/
def allOnesMatrix {N : ℕ} : Matrix (Fin N) (Fin N) ℝ :=
  fun _ _ => 1

/-- The diagonal matrix D_b from the admitted resolvent factorization. -/
def resolventDiagonalMatrix {N : ℕ} (b : ℝ) (nodes : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => 1 / (nodes i + b))

/-- The finite-node matrix of the all-entry source-channel resolvent kernel. -/
def resolventChannelMatrix {N : ℕ} (b : ℝ) (nodes : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => resolventChannelKernel b (nodes i) (nodes j)

/-- Exact statement of the admitted resolvent formula and its matrix factorization. -/
def resolventChannelKernelFormula : Prop :=
  (∀ (b lam mu : ℝ),
    resolventChannelKernel b lam mu =
      4 * (lam + mu + b) / ((lam + b) * (mu + b) * (lam + mu))) ∧
  (∀ (N : ℕ) (b : ℝ) (nodes : Fin N → ℝ),
    Function.Injective nodes →
      resolventChannelMatrix b nodes =
        (4 : ℝ) •
          (resolventDiagonalMatrix b nodes *
            (allOnesMatrix + b • cauchyMatrix nodes) *
            resolventDiagonalMatrix b nodes))

/-- The standard real symmetric congruence encoding of inertia (positive, negative, zero). -/
def hasInertia {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (positive negative zeroCount : ℕ) : Prop :=
  Matrix.IsSymm M ∧
    ∃ (Q : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ),
      Matrix.det Q ≠ 0 ∧
        M = Q.transpose * Matrix.diagonal d * Q ∧
        (Finset.univ.filter (fun i => 0 < d i)).card = positive ∧
        (Finset.univ.filter (fun i => d i < 0)).card = negative ∧
        (Finset.univ.filter (fun i => d i = 0)).card = zeroCount

/-- The Cauchy identity used by the negative pole channel. -/
def cauchyInverseOnesIdentity {N : ℕ} (nodes : Fin N → ℝ) : Prop :=
  dotProduct (fun _ : Fin N => (1 : ℝ))
      (Matrix.mulVec ((cauchyMatrix nodes)⁻¹) (fun _ : Fin N => (1 : ℝ))) =
    2 * ∑ i, nodes i

/-- Exact inertia assertions for the two elementary pole channels. -/
def elementaryChannelInertias : Prop :=
  ∀ (N : ℕ) (nodes : Fin N → ℝ),
    (∀ i, (1 / 2 : ℝ) < nodes i) →
      Function.Injective nodes →
        hasInertia (resolventChannelMatrix (1 / 2 : ℝ) nodes) N 0 0 ∧
          hasInertia (resolventChannelMatrix (-1 / 2 : ℝ) nodes) 1 (N - 1) 0 ∧
            cauchyInverseOnesIdentity nodes

/-- The even exponential translation-correlation kernel, including its diagonal continuation. -/
def evenTranslationCorrelation (ell lam mu : ℝ) : ℝ :=
  if lam = mu then
    Real.exp (-lam * ell) * (lam⁻¹ + ell)
  else
    2 * (lam * Real.exp (-mu * ell) - mu * Real.exp (-lam * ell)) /
      (lam ^ 2 - mu ^ 2)

/-- The prime-side matrix supplied by a scalar von Mangoldt atom. -/
def primeAtomMatrix (a ell : ℝ) (rates : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (-2 * a) • Matrix.of (fun i j => evenTranslationCorrelation ell (rates i) (rates j))

/-- Exact determinant and inertia assertion for the prime 3 atom at rates 1 and 2. -/
def explicitTwoNodePrimeAtom : Prop :=
  let ell : ℝ := Real.log 3
  let a : ℝ := Real.log 3 / Real.sqrt 3
  let rates : Fin 2 → ℝ := ![(1 : ℝ), 2]
  let K3 : Matrix (Fin 2) (Fin 2) ℝ := primeAtomMatrix a ell rates
  Matrix.det K3 =
      (a ^ 2 / 729) * (54 * (1 + ell) * (1 + 2 * ell) - 400) ∧
      Matrix.det K3 < 0 ∧
      hasInertia K3 1 1 0

/-- The constant archimedean channel. -/
def constantChannelKernel (lam mu : ℝ) : ℝ :=
  -2 * Real.log Real.pi / (lam + mu)

/-- The exact, unsplit digamma-channel series from the admitted expansion. -/
def gammaChannelKernel (lam mu : ℝ) : ℝ :=
  -2 * Real.eulerMascheroniConstant / (lam + mu) +
    ∑' k : ℕ,
      (2 / (((k : ℝ) + 1) * (lam + mu)) -
        4 *
            (lam + mu + (2 * (k : ℝ) + 1 / 2)) /
              ((lam + (2 * (k : ℝ) + 1 / 2)) *
                (mu + (2 * (k : ℝ) + 1 / 2)) * (lam + mu)))

/-- The complete two-node archimedean kernel block. -/
def archimedeanKernel (lam mu : ℝ) : ℝ :=
  resolventChannelKernel (1 / 2 : ℝ) lam mu +
    resolventChannelKernel (-1 / 2 : ℝ) lam mu +
      constantChannelKernel lam mu + gammaChannelKernel lam mu

/-- The matrix of the complete archimedean block at finite rates. -/
def archimedeanMatrix {N : ℕ} (rates : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => archimedeanKernel (rates i) (rates j)

/-- Exact sign, determinant interval, and inertia assertion for the archimedean block. -/
def totalArchimedeanBlockIndefinite : Prop :=
  let rates : Fin 2 → ℝ := ![(3 / 2 : ℝ), 7 / 2]
  let Kinf : Matrix (Fin 2) (Fin 2) ℝ := archimedeanMatrix rates
  0 < Kinf 0 0 ∧
    0 < Kinf 1 1 ∧
      (-0.195424 : ℝ) ≤ Matrix.det Kinf ∧
        Matrix.det Kinf ≤ (-0.195423 : ℝ) ∧
          Matrix.det Kinf < 0 ∧
            hasInertia Kinf 1 1 0

end
end MathlibPlus.Open.Analysis
