import Mathlib

namespace MathlibPlus.Open.K0132

open scoped Topology BigOperators

/-- The family with a varying leading coefficient and fixed lower coefficients. -/
def affineLeadingFamily {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (d : ℕ) (β : 𝕜 → 𝕜) (c : Fin d → 𝕜) (b x : 𝕜) : 𝕜 :=
  β b * x ^ d + ∑ k : Fin d, c k * x ^ (k : ℕ)

/-- Affine leading-coefficient root flow for every differentiable simple root branch. -/
def affineLeadingCoefficientRootFlow : Prop :=
  ∀ {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (d : ℕ) (β : 𝕜 → 𝕜) (c : Fin d → 𝕜) (b : 𝕜)
    (r : 𝕜 → 𝕜) (v : 𝕜),
    HasDerivAt β 1 b →
    (∀ᶠ t in 𝓝 b, affineLeadingFamily d β c t (r t) = 0) →
    HasDerivAt r v b →
    deriv (fun x : 𝕜 => affineLeadingFamily d β c b x) (r b) ≠ 0 →
    v = -(r b) ^ d /
      deriv (fun x : 𝕜 => affineLeadingFamily d β c b x) (r b)

/-- The squared Vandermonde of a finite indexed subset. -/
def finiteVandermondeSq {𝕜 : Type*} [CommRing 𝕜]
    {d : ℕ} (x : Fin d → 𝕜) (s : Finset (Fin d)) : 𝕜 :=
  ∏ i ∈ s, ∏ j ∈ s.filter (fun j => i < j), (x i - x j) ^ 2

/-- The Vandermonde-squared subset partition function. -/
def particlePartition {𝕜 : Type*} [CommRing 𝕜]
    (d r : ℕ) (x : Fin d → 𝕜) (w : Fin d → 𝕜) : 𝕜 :=
  ∑ s ∈ (Finset.univ : Finset (Fin d)).powerset.filter (fun s => s.card = r),
    finiteVandermondeSq x s * ∏ j ∈ s, w j

/-- The node polynomial whose logarithmic derivative supplies the dual weights. -/
def nodePolynomial {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {d : ℕ} (x : Fin d → 𝕜) (z : 𝕜) : 𝕜 :=
  ∏ j : Fin d, (z - x j)

/-- Complementation duality for the Vandermonde-squared particle partition function. -/
def finiteParticleHoleDuality : Prop :=
  ∀ {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (d r : ℕ) (x : Fin d → 𝕜) (w : Fin d → 𝕜),
    r ≤ d →
    Function.Injective x →
    (∀ j, w j ≠ 0) →
    let A : 𝕜 → 𝕜 := nodePolynomial x
    let wHat : Fin d → 𝕜 := fun j => (w j * (deriv A (x j)) ^ 2)⁻¹
    particlePartition d r x w =
      finiteVandermondeSq x (Finset.univ : Finset (Fin d)) *
        (∏ j : Fin d, w j) * particlePartition d (d - r) x wHat

/-- Reciprocal central norm identity at odd-cardinality half filling. -/
def reciprocalCentralNormHalfFilling : Prop :=
  ∀ {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (n : ℕ) (x : Fin (2 * n + 1) → 𝕜) (w : Fin (2 * n + 1) → 𝕜),
    Function.Injective x →
    (∀ j, w j ≠ 0) →
    let d := 2 * n + 1
    let A : 𝕜 → 𝕜 := nodePolynomial x
    let wHat : Fin d → 𝕜 := fun j => (w j * (deriv A (x j)) ^ 2)⁻¹
    let h : (Fin d → 𝕜) → 𝕜 := fun u =>
      particlePartition d (n + 1) x u / particlePartition d n x u
    h w * h wHat = 1

/-- Dual root-functional weights, and their half-filled ensemble realization by root velocities. -/
def dualRootWeightsAffineVelocities : Prop :=
  ∀ {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (n d : ℕ) (β : 𝕜 → 𝕜) (c : Fin d → 𝕜) (b : 𝕜)
    (roots : Fin d → 𝕜 → 𝕜) (velocities : Fin d → 𝕜),
    d = 2 * n + 1 →
    HasDerivAt β 1 b →
    (∀ j, HasDerivAt (roots j) (velocities j) b) →
    (∀ j, ∀ᶠ t in 𝓝 b, affineLeadingFamily d β c t (roots j t) = 0) →
    (∀ y : 𝕜,
      affineLeadingFamily d β c b y =
        β b * ∏ j : Fin d, (y - roots j b)) →
    (∀ j, deriv (fun y : 𝕜 => affineLeadingFamily d β c b y) (roots j b) ≠ 0) →
    (∀ j, roots j b ≠ 0) →
    (∀ j, velocities j =
      -(roots j b) ^ d /
        deriv (fun y : 𝕜 => affineLeadingFamily d β c b y) (roots j b)) ∧
    (∀ j,
      (β b) ^ 2 *
          (roots j b *
            (deriv (fun y : 𝕜 => affineLeadingFamily d β c b y) (roots j b)) ^ 2)⁻¹ =
        (β b) ^ 2 * (velocities j) ^ 2 / (roots j b) ^ (2 * d + 1)) ∧
    (let dualW : Fin d → 𝕜 := fun j =>
      (β b) ^ 2 *
        (roots j b *
          (deriv (fun y : 𝕜 => affineLeadingFamily d β c b y) (roots j b)) ^ 2)⁻¹
     let velocityW : Fin d → 𝕜 := fun j =>
       (β b) ^ 2 * (velocities j) ^ 2 / (roots j b) ^ (2 * d + 1)
     particlePartition d n (fun j => roots j b) dualW =
       particlePartition d n (fun j => roots j b) velocityW ∧
     particlePartition d (n + 1) (fun j => roots j b) dualW =
       particlePartition d (n + 1) (fun j => roots j b) velocityW)

end MathlibPlus.Open.K0132
