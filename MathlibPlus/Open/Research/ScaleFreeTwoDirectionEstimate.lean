import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

noncomputable section

/-- The Euclidean norm on two-dimensional real vectors. -/
def twoVectorNorm (v : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (Finset.sum Finset.univ (fun i => v i ^ 2))

/-- The operator norm induced by the Euclidean norm on two-dimensional vectors. -/
def twoOperatorNorm (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ v : Fin 2 → ℝ,
    twoVectorNorm (Matrix.mulVec M v) ≤ c * twoVectorNorm v}

/-- The zero-diagonal Jacobi transfer matrix at index `j`. -/
def zeroDiagonalTransferMatrix (a : ℕ → ℝ) (x : ℝ) (j : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![x / a (j + 1), -(a j / a (j + 1));
      1, 0]

/-- The ordered product `T_{A+n} ⋯ T_A`. -/
def zeroDiagonalTransferProduct (a : ℕ → ℝ) (x : ℝ) (A n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Nat.rec
    (motive := fun _ => Matrix (Fin 2) (Fin 2) ℝ)
    (zeroDiagonalTransferMatrix a x A)
    (fun n product =>
      zeroDiagonalTransferMatrix a x (A + n + 1) * product)
    n

/-- The logarithmic total variation on the edge indices from `A` through `B`. -/
def logarithmicTotalVariation (a : ℕ → ℝ) (A B : ℕ) : ℝ :=
  Finset.sum (Finset.Icc A B) (fun j => abs (Real.log (a (j + 1) / a j)))

/-- The elliptic-block condition written without introducing an unavailable minimum carrier. -/
def ellipticBlockCondition (a : ℕ → ℝ) (x ρ : ℝ) (A B : ℕ) : Prop :=
  ∀ j, A ≤ j → j ≤ B + 1 → abs x ≤ 2 * ρ * a j

/-- The common scale-free upper bound for both transfer directions. -/
def twoDirectionTransferBound (a : ℕ → ℝ) (x ρ : ℝ) (A B : ℕ) : Prop :=
  let T := zeroDiagonalTransferProduct a x A (B - A)
  let Λρ := 2 / (1 - ρ ^ 2)
  let bound := ((1 + ρ) / (1 - ρ)) *
    Real.exp (Λρ * logarithmicTotalVariation a A B)
  twoOperatorNorm T ^ 2 ≤ bound ∧
    twoOperatorNorm (T⁻¹) ^ 2 ≤ bound

/-- Scale-free two-direction estimate for the Jacobi transfer product. -/
def scaleFreeTwoDirectionEstimate : Prop :=
  ∀ (a : ℕ → ℝ) (x ρ : ℝ) (A B : ℕ),
    0 ≤ ρ →
    ρ < 1 →
    (∀ j, 0 < a j) →
    A ≤ B →
    ellipticBlockCondition a x ρ A B →
    twoDirectionTransferBound a x ρ A B ∧
      (∀ s : ℝ, 0 < s →
        twoDirectionTransferBound a x ρ A B ↔
          twoDirectionTransferBound (fun j => s * a j) (s * x) ρ A B)

end
end MathlibPlus.Open.Research
