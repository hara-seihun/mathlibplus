import Mathlib

namespace MathlibPlus.Open.Analysis.K0019RadialPascal

open scoped BigOperators

noncomputable def radialTransportEntry (q : ℝ) (i p : ℕ) : ℝ :=
  if i ≤ p then
    q ^ i * (Nat.choose p i : ℝ) * ((1 - q) / 2) ^ (p - i)
  else 0

noncomputable def radialPascalMatrix (q : ℝ) : Matrix ℕ ℕ ℝ :=
  fun i p => radialTransportEntry q i p

noncomputable def profileSum {n : ℕ} (P : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, P i

noncomputable def profileFactorial (n : ℕ) : ℝ :=
  ∏ i : Fin n, (i.val.factorial : ℝ)

noncomputable def profileVandermonde {n : ℕ} (P : Fin n → ℕ) : ℝ :=
  Finset.prod (Finset.univ : Finset (Fin n)) (fun i =>
    Finset.prod (Finset.Ioi i) (fun j => ((P j - P i : ℕ) : ℝ)))

noncomputable def initialProfile (n : ℕ) : Fin n → ℕ := fun i => i.val

noncomputable def oneHookProfile (n : ℕ) : Fin n → ℕ :=
  fun i => if i.val < n - 1 then i.val else n

abbrev IncreasingProfile (n : ℕ) := {P : Fin n → ℕ // StrictMono P}

/-- Claim 7552: the infinite upper-triangular Pascal transport matrix has the
exact displayed entry formula. -/
def pascalTransportMatrix_claim7552 : Prop :=
  ∀ (q : ℝ), 0 < q → q < 1 →
    ∀ i p : ℕ,
      radialPascalMatrix q i p =
        if p ≥ i then
          q ^ i * (Nat.choose p i : ℝ) * ((1 - q) / 2) ^ (p - i)
        else 0

/-- Claim 7556: every finite minor of the explicit transport matrix is
nonnegative. -/
def transportTotalNonnegative_claim7556 : Prop :=
  ∀ (q : ℝ), 0 < q → q < 1 →
    ∀ (n : ℕ) (I J : Fin n → ℕ),
      StrictMono I → StrictMono J →
      0 ≤ Matrix.det (fun i j : Fin n => radialTransportEntry q (I i) (J j))

/-- Claim 7557: the initial principal profile has the displayed Pascal minor,
including the positive Vandermonde factor. -/
def explicitInitialProfilePascalMinor_claim7557 : Prop :=
  ∀ (q : ℝ), 0 < q → q < 1 →
    ∀ (n : ℕ) (P : Fin n → ℕ), StrictMono P →
      let α := (1 - q) / 2
      let S := n * (n - 1) / 2
      0 < profileVandermonde P ∧
      Matrix.det (fun i j : Fin n =>
          radialTransportEntry q i.val (P j)) =
        q ^ S * α ^ (profileSum P - S) * profileVandermonde P /
          profileFactorial n

/-- Claim 7561: the one-hook to initial-profile Pascal-minor ratio. -/
def oneHookPascalMinorRatio_claim7561 : Prop :=
  ∀ (q : ℝ), 0 < q → q < 1 →
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (P : Fin n → ℕ), StrictMono P →
        let α := (1 - q) / 2
        let S := n * (n - 1) / 2
        Matrix.det (fun i j : Fin n =>
            radialTransportEntry q (oneHookProfile n i) (P j)) /
            Matrix.det (fun i j : Fin n =>
              radialTransportEntry q (initialProfile n i) (P j)) =
          (q / α) * ((profileSum P - S : ℕ) : ℝ) / (n : ℝ)

end MathlibPlus.Open.Analysis.K0019RadialPascal
