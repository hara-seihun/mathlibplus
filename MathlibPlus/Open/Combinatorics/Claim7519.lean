import Mathlib

open BigOperators

namespace MathlibPlus.Open.Combinatorics.Claim7519

/-- The load of a fold type. -/
def foldLoad (a : ℕ × ℕ) : ℕ := 2 * a.1 + a.2

/-- The number of fold types with positive load ell. -/
def foldTypeCount (ell : ℕ) : ℕ := ell / 2 + 1

/-- A finitely supported one-height multiplicity function, with no empty fold. -/
structure OneHeightPresentation where
  multiplicity : (ℕ × ℕ) →₀ ℕ
  excludesEmpty : multiplicity (0, 0) = 0

/-- The total load of a one-height presentation. -/
def oneHeightLoad (X : OneHeightPresentation) : ℕ :=
  ∑ a ∈ X.multiplicity.support, X.multiplicity a * foldLoad a

/-- The one-height cycle weight. -/
noncomputable def oneHeightWeight (X : OneHeightPresentation) : ℝ :=
  ∏ a ∈ X.multiplicity.support,
    (1 : ℝ) /
      (Nat.factorial (X.multiplicity a) *
        (foldLoad a * foldTypeCount (foldLoad a)) ^ X.multiplicity a)

/-- A finitely supported family of one-height presentations indexed by actual primes. -/
structure EulerScarweave where
  heights : Nat.Primes →₀ ((ℕ × ℕ) →₀ ℕ)
  excludesEmpty : ∀ p, heights p (0, 0) = 0

/-- The local presentation at a prime. -/
def localPresentation (X : EulerScarweave) (p : Nat.Primes) : OneHeightPresentation :=
  ⟨X.heights p, X.excludesEmpty p⟩

/-- The seam integer of an Euler Scarweave. -/
def seamInteger (X : EulerScarweave) : ℕ :=
  ∏ p ∈ X.heights.support, p.1 ^ oneHeightLoad (localPresentation X p)

/-- The global Scarweave weight. -/
noncomputable def scarweaveWeight (X : EulerScarweave) : ℝ :=
  ∏ p ∈ X.heights.support, oneHeightWeight (localPresentation X p)

/-- The complex summand in the Scarweave partition function. -/
noncomputable def partitionTerm (σ : ℂ) (X : EulerScarweave) : ℂ :=
  (scarweaveWeight X : ℂ) * Complex.cpow (seamInteger X : ℂ) (-σ)

/-- The absolutely convergent Dirichlet series over positive integers. -/
noncomputable def zetaSeries (σ : ℂ) : ℂ :=
  ∑' n : ℕ, if n = 0 then 0 else Complex.cpow (n : ℂ) (-σ)

/-- The Scarweave partition function equals the zeta series in its half-plane. -/
def scarweavePartitionEqualsZeta_claim7519 : Prop :=
  ∀ σ : ℂ, 1 < σ.re →
    Summable (fun X : EulerScarweave => ‖partitionTerm σ X‖) ∧
      (∑' X : EulerScarweave, partitionTerm σ X) = zetaSeries σ ∧
      zetaSeries σ = riemannZeta σ

end MathlibPlus.Open.Combinatorics.Claim7519
