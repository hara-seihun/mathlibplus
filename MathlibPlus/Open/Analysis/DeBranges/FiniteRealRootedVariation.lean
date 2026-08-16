import Mathlib

namespace MathlibPlus.Open.Analysis.DeBranges

noncomputable def finiteShiftedPolynomial
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (z : ℂ) : ℂ :=
  c * ∏ j : Fin n, (z - (roots j : ℂ))

def finiteRealVector (n : ℕ) (x : ℝ) (i : Fin n) : ℝ :=
  x ^ (i : ℕ)

def finiteComplexVector (n : ℕ) (z : ℂ) (i : Fin n) : ℂ :=
  z ^ (i : ℕ)

noncomputable def finiteRadius (n : ℕ) (roots : Fin n → ℝ) (ω x : ℝ) : ℝ :=
  2 * ω * ∑ j : Fin n, 1 / ((x - roots j) ^ 2 + ω ^ 2)

noncomputable def finiteWeight
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (ω x : ℝ) : ℝ :=
  (Complex.normSq
      (finiteShiftedPolynomial n c roots ((x : ℂ) + (ω : ℂ) * Complex.I)))⁻¹

noncomputable def finiteGram
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (ω : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    ∫ x : ℝ,
      finiteRealVector n x i * finiteRealVector n x j *
        finiteWeight n c roots ω x

noncomputable def finiteGramVariation
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (ω : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    ∫ x : ℝ,
      finiteRadius n roots ω x * finiteRealVector n x i *
        finiteRealVector n x j * finiteWeight n c roots ω x

noncomputable def finiteRealRootedGramVariation : Prop :=
  ∀ (n : ℕ) (c : ℂ) (roots : Fin n → ℝ),
    0 < n → c ≠ 0 →
      ∀ ω : ℝ, 0 < ω →
        (∀ x : ℝ,
          Complex.normSq
              (finiteShiftedPolynomial n c roots
                ((x : ℂ) + (ω : ℂ) * Complex.I)) =
            Complex.normSq c *
              ∏ j : Fin n, ((x - roots j) ^ 2 + ω ^ 2)) ∧
        (∀ x : ℝ,
          HasDerivAt
            (fun t : ℝ => finiteWeight n c roots t x)
            (-finiteRadius n roots ω x * finiteWeight n c roots ω x) ω) ∧
        (∀ x : ℝ, 0 < finiteRadius n roots ω x) ∧
        HasDerivAt
          (fun t : ℝ => finiteGram n c roots t)
          (-finiteGramVariation n c roots ω) ω ∧
        -(deriv (fun t : ℝ => finiteGram n c roots t) ω) =
          finiteGramVariation n c roots ω ∧
        Matrix.PosDef (finiteGramVariation n c roots ω)

noncomputable def finiteH
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (ω : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (finiteGram n c roots ω)⁻¹

noncomputable def finiteE
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (ω : ℝ) (z : ℂ) : ℂ :=
  finiteShiftedPolynomial n c roots (z + (ω : ℂ) * Complex.I)

noncomputable def finiteKernel
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (ω : ℝ)
    (w z : ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    finiteComplexVector n z i *
      (finiteH n c roots ω i j : ℂ) *
      star (finiteComplexVector n w j)

noncomputable def finiteComplexPositiveSemidefinite
    {m : Type} [Fintype m] (A : Matrix m m ℂ) : Prop :=
  (∀ i j, A i j = star (A j i)) ∧
    ∀ z : m → ℂ,
      0 ≤
        (∑ i, ∑ j, star (z i) * A i j * z j).re

noncomputable def finiteKernelDerivativeGram
    (n : ℕ) (c : ℂ) (roots : Fin n → ℝ) (ω : ℝ)
    {m : ℕ} (z : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun a b =>
    deriv (fun t : ℝ =>
      finiteKernel n c roots t (z a) (z b)) ω

noncomputable def finiteRealRootedPositiveKernelVariation : Prop :=
  ∀ (n : ℕ) (c : ℂ) (roots : Fin n → ℝ),
    0 < n → c ≠ 0 →
      ∀ ω : ℝ, 0 < ω →
        finiteH n c roots ω = (finiteGram n c roots ω)⁻¹ ∧
        HasDerivAt
          (fun t : ℝ => finiteH n c roots t)
          (-(finiteH n c roots ω *
              deriv (fun t : ℝ => finiteGram n c roots t) ω *
              finiteH n c roots ω)) ω ∧
        deriv (fun t : ℝ => finiteH n c roots t) ω =
          -(finiteH n c roots ω *
              deriv (fun t : ℝ => finiteGram n c roots t) ω *
              finiteH n c roots ω) ∧
        Matrix.PosSemidef (deriv (fun t : ℝ => finiteH n c roots t) ω) ∧
        (∀ w z : ℂ,
          deriv (fun t : ℝ => finiteKernel n c roots t w z) ω =
            ∫ x : ℝ,
              (finiteRadius n roots ω x : ℂ) *
                finiteKernel n c roots ω (x : ℂ) z *
                finiteKernel n c roots ω w (x : ℂ) *
                (Complex.normSq (finiteE n c roots ω (x : ℂ)))⁻¹) ∧
        (∀ {m : ℕ} (z : Fin m → ℂ),
          finiteComplexPositiveSemidefinite
            (finiteKernelDerivativeGram n c roots ω z))

end MathlibPlus.Open.Analysis.DeBranges
