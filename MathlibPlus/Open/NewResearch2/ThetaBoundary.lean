import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0201

/-- Claim 18773: the displayed Abel-flat extension is smooth at its boundary,
with every boundary jet zero, although it is not the zero function. -/
def claim18773_abelFlatMode : Prop :=
  let f : ℝ → ℝ := fun x ↦
    if x < 1 then Real.exp (-(1 + x) / (1 - x)) else 0
  ContDiffAt ℝ (⊤ : WithTop ℕ∞) f 1 ∧
    (∀ k : ℕ, iteratedDeriv k f 1 = 0) ∧
    f 0 ≠ 0

end MathlibPlus.Open.NewResearch2.R0201

namespace MathlibPlus.Open.NewResearch2.R0202

/-- Claim 18775: the listed independent failures are all present in concrete
finite-dimensional, Abel-flat, and even-function models.  The comparison-map
component is expressed by the non-uniqueness of a prime-to-shell map when the
shell equation map itself is zero. -/
def claim18775_gaalPremiseFailures : Prop :=
  (∀ r m : ℕ, r < m →
    ∀ A : Fin r → Fin m → ℝ,
      ∃ v : Fin m → ℝ,
        v ≠ 0 ∧ ∀ i : Fin r, ∑ j : Fin m, A i j * v j = 0) ∧
  (∀ r m : ℕ, r < m →
    ∀ A : Fin r → Fin m → ℝ,
      ∃ v : Fin m → ℝ,
        v ≠ 0 ∧ ∀ i : Fin r,
          ∑ j : Fin m, A i j * Real.sinh (v j) = 0) ∧
  MathlibPlus.Open.NewResearch2.R0201.claim18773_abelFlatMode ∧
  (let g : ℂ → ℂ := fun z ↦ z ^ 2 - 1
   (∀ j : ℕ, iteratedDeriv (2 * j + 1) g 0 = 0) ∧
     ∃ z : ℂ, g z = 0 ∧ z.re ≠ 0) ∧
  (let zeroMap : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) := 0
   ∃ C₁ C₂ : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ),
     C₁ ≠ C₂ ∧ zeroMap.comp C₁ = zeroMap.comp C₂)

end MathlibPlus.Open.NewResearch2.R0202

namespace MathlibPlus.Open.NewResearch2.R0202

/-- Claim 18780: the constant-one modular coefficient sequence is not in any
exponentially weighted shell class, and it is not at finite distance from a
localized sequence in any witnessing localized weight. -/
def claim18780_localizedPerturbationsMissModularPoint : Prop :=
  let a : ℕ → ℝ := fun n ↦ Real.pi * (n : ℝ) ^ 2
  let localizedAt : (ℕ → ℝ) → ℝ → Prop := fun c δ ↦
    0 < δ ∧
      (∑' n : ℕ,
        ENNReal.ofReal (|c n| * a n * Real.exp (δ * a n))) < ⊤
  let one : ℕ → ℝ := fun _ ↦ 1
  (¬ ∃ δ : ℝ, localizedAt one δ) ∧
    (∀ c : ℕ → ℝ, ∀ δ : ℝ, localizedAt c δ →
      ¬ (∑' n : ℕ,
          ENNReal.ofReal (|1 - c n| * a n * Real.exp (δ * a n))) < ⊤)

end MathlibPlus.Open.NewResearch2.R0202
