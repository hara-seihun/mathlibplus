import Mathlib

namespace MathlibPlus.Open.Analysis.ProjectiveGauss

/-- The outer folded reciprocal-heat-kernel Gauss curve is increasing and
strictly convex in the stated affine-orientation form, and all translated
square-flag barycenters have positive orientation. -/
def outerConvexityAndTranslatedFlags_claim573 : Prop :=
  let K : ℝ → ℝ → ℝ := fun q l =>
    Real.rpow l (-(5 : ℝ) / 4) * Real.exp (-q / l) +
      Real.rpow l ((5 : ℝ) / 4) * Real.exp (-q * l)
  let D : (ℝ → ℝ) → ℝ → ℝ := fun u l => l * deriv u l
  let f : ℝ → ℝ → ℝ := fun q l => D (fun u => K q u) l / K q l
  let g : ℝ → ℝ → ℝ := fun q l => D (fun u => D (fun v => K q v) u) l / K q l
  let h : ℝ → ℝ → ℝ := fun q l =>
    D (fun u => D (fun v => D (fun w => K q w) v) u) l / K q l
  let fq : ℝ → ℝ → ℝ := fun l q => deriv (fun x => f x l) q
  let rho : ℝ → ℝ → ℝ := fun l q => deriv (fun x => g x l) q / fq l q
  let sigma : ℝ → ℝ → ℝ := fun l q => deriv (fun x => h x l) q / fq l q
  let orient : (ℝ × ℝ) → (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun a b c =>
    (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)
  let squareKnot : ℕ → ℕ → ℝ := fun n j => Real.pi * ((n + j : ℕ) : ℝ) ^ 2
  let mass : ℝ → ℝ → ℝ → ℝ := fun l a b => ∫ q in a..b, fq l q
  let barycenter : ℝ → ℝ → ℝ → ℝ × ℝ := fun l a b =>
    ((mass l a b)⁻¹ * ∫ q in a..b, fq l q * rho l q,
      (mass l a b)⁻¹ * ∫ q in a..b, fq l q * sigma l q)
  ∀ l : ℝ, 1 < l →
    (∀ q : ℝ, 4 * Real.pi ≤ q → 0 < fq l q) ∧
    (∀ x y : ℝ, 4 * Real.pi ≤ x → x < y → rho l x < rho l y) ∧
    (∀ x y z : ℝ, 4 * Real.pi ≤ x → x < y → y < z →
      0 < orient (rho l x, sigma l x) (rho l y, sigma l y) (rho l z, sigma l z)) ∧
    ∀ n : ℕ, 2 ≤ n →
      let q₀ := squareKnot n 0
      let q₁ := squareKnot n 1
      let q₂ := squareKnot n 2
      let q₃ := squareKnot n 3
      0 < mass l q₀ q₁ ∧ 0 < mass l q₁ q₂ ∧ 0 < mass l q₂ q₃ ∧
        0 < orient (barycenter l q₀ q₁) (barycenter l q₁ q₂)
          (barycenter l q₂ q₃)

end MathlibPlus.Open.Analysis.ProjectiveGauss
