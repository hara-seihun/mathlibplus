import Mathlib

open scoped BigOperators Topology
open Filter

namespace MathlibPlus.Open.ResearchFormalization.O0327

noncomputable section

/-- The horizontal graph carrier `γ(t) = t + i y(t)`. -/
def graphPoint (y : ℝ → ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) + Complex.I * (y t : ℂ)

/-- The uniform, eventual meaning of a bound over a finite moving index set. -/
def uniformEventualBigO {ι : ℕ → Type*}
    (f : ∀ m, ι m → ℝ) (g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ m : ℕ in atTop, ∀ i : ι m, |f m i| ≤ C * g m

/-- The curvature phase correction for one moving finite node array. -/
def curvaturePhaseCorrection {q : ℕ}
    (y : ℝ → ℝ) (u : Fin q → ℝ) (j : Fin q) : ℝ :=
  ∑ k ∈ (Finset.univ.erase j),
    Complex.arg
      ((graphPoint y (u j) - graphPoint y (u k)) /
        ((u j - u k : ℝ) : ℂ))

/-- The coordinate `ℓ¹` norm of the gradient of a curvature correction. -/
def curvaturePhaseGradientL1 {q : ℕ}
    (y : ℝ → ℝ) (u : Fin q → ℝ) (j : Fin q) : ℝ :=
  ∑ k : Fin q,
    ‖fderiv ℝ (fun v : Fin q → ℝ => curvaturePhaseCorrection y v j) u
      (Pi.single k 1)‖

/-- Ordered nodes over a horizontal interval of length `S`, with the candidate
spacing and count used by the half-turn construction. -/
def scaledCandidateNodes
    (L S : ℕ → ℝ) (a : ℕ → ℝ) (n : ℕ → ℕ)
    (t : ∀ m, Fin (n m + 1) → ℝ) : Prop :=
  ∃ Cmin Cgap Ccount : ℝ,
    0 < Cmin ∧ 0 ≤ Cgap ∧ 0 ≤ Ccount ∧
    (∀ᶠ m : ℕ in atTop,
      (∀ i j : Fin (n m + 1), i.val < j.val → t m i < t m j) ∧
      (∀ j : Fin (n m),
        Cmin / L m ≤ t m (Fin.succ j) - t m (Fin.castSucc j) ∧
        t m (Fin.succ j) - t m (Fin.castSucc j) ≤ Cgap / L m) ∧
      (∀ j : Fin (n m + 1), t m j ∈ Set.Icc (a m) (a m + S m)) ∧
      (n m : ℝ) ≤ Ccount * L m * S m)

/-- The uniform, eventual meaning of a bound on the graph's horizontal box. -/
def uniformEventualBigOOn
    (f : ℕ → ℝ → ℝ) (g a S : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ m : ℕ in atTop,
      ∀ u ∈ Set.Icc (a m) (a m + S m), |f m u| ≤ C * g m

/-- Claim 15443: scaled-`C²` curvature-phase corrections.  The three
conclusions are the uniform eventual forms of `|χ_j| = O(L)`,
`‖∇χ_j‖₁ = O(L/S)`, and `χ_{j+1} - χ_j = O(S⁻¹)`. -/
def claim15443_scaledC2CurvaturePhaseCorrections : Prop :=
  ∀ (L S a : ℕ → ℝ) (y : ℕ → ℝ → ℝ)
    (n : ℕ → ℕ) (t : ∀ m, Fin (n m + 1) → ℝ),
    Tendsto L atTop atTop →
    (∀ᶠ m : ℕ in atTop, 0 < L m ∧ 0 < S m) →
    scaledCandidateNodes L S a n t →
    (∀ᶠ m : ℕ in atTop,
      DifferentiableOn ℝ (y m) (Set.Icc (a m) (a m + S m)) ∧
        DifferentiableOn ℝ (deriv (y m))
          (Set.Icc (a m) (a m + S m))) →
    uniformEventualBigOOn
      (fun m (u : ℝ) => deriv (y m) u)
      (fun m => (S m)⁻¹) a S →
    uniformEventualBigOOn
      (fun m (u : ℝ) => deriv (deriv (y m)) u)
      (fun m => (S m)⁻¹ * (S m)⁻¹) a S →
    (uniformEventualBigO
      (fun m j => curvaturePhaseCorrection (y m) (t m) j)
      L ∧
      uniformEventualBigO
        (fun m j => curvaturePhaseGradientL1 (y m) (t m) j)
        (fun m => L m / S m) ∧
      uniformEventualBigO
        (fun m j =>
          curvaturePhaseCorrection (y m) (t m) (Fin.succ j) -
            curvaturePhaseCorrection (y m) (t m) (Fin.castSucc j))
        (fun m => (S m)⁻¹))

end

end MathlibPlus.Open.ResearchFormalization.O0327
