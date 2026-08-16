import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open

/-- A revealed-or-unrevealed coordinate observation. -/
def Observation (n : ℕ) := Fin n → Option Bool

/-- The sign returned by a Boolean depth-one component. -/
def rademacher (b : Bool) : ℝ := if b then 1 else -1

/-- Two oracle assignments agree on the coordinates in `A`. -/
def agreesOn {n : ℕ} (A : Finset (Fin n))
    (ω ω' : Fin n → Bool) : Prop :=
  ∀ i ∈ A, ω i = ω' i

/-- Coordinates whose answers have been revealed in a partial observation. -/
def observed {n : ℕ} (h : Observation n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ b, h i = some b)

/-- Uniform conditional expectation given the answers on `A`. -/
noncomputable def conditionalMean {n : ℕ}
    (F : (Fin n → Bool) → ℝ) (A : Finset (Fin n))
    (ω : Fin n → Bool) : ℝ :=
  let denominator : ℝ :=
    ∑ ω' : Fin n → Bool, if agreesOn A ω ω' then 1 else 0
  (∑ ω' : Fin n → Bool,
      if agreesOn A ω ω' then F ω' else 0) / denominator

/-- Uniform conditional variance given the answers on `A`. -/
noncomputable def conditionalVariance {n : ℕ}
    (F : (Fin n → Bool) → ℝ) (A : Finset (Fin n))
    (ω : Fin n → Bool) : ℝ :=
  let μ := conditionalMean F A ω
  let denominator : ℝ :=
    ∑ ω' : Fin n → Bool, if agreesOn A ω ω' then 1 else 0
  (∑ ω' : Fin n → Bool,
      if agreesOn A ω ω' then (F ω' - μ) ^ 2 else 0) / denominator

/-- A legal adaptive policy chooses an unrevealed coordinate whenever one exists. -/
def LegalPolicy {n : ℕ} (π : Observation n → Fin n) : Prop :=
  ∀ h : Observation n, (∃ i : Fin n, h i = none) → h (π h) = none

/-- The observation after `t` actions of a policy on oracle assignment `ω`. -/
def observationAt {n : ℕ} (π : Observation n → Fin n)
    (ω : Fin n → Bool) : ℕ → Observation n
  | 0 => fun _ => none
  | t + 1 =>
      let h := observationAt π ω t
      Function.update h (π h) (some (ω (π h)))

/-- Expected posterior variance at one root-inclusive time. -/
noncomputable def expectedPosteriorVarianceAt {n : ℕ}
    (F : (Fin n → Bool) → ℝ) (π : Observation n → Fin n) (t : ℕ) : ℝ :=
  (∑ ω : Fin n → Bool,
      conditionalVariance F (observed (observationAt π ω t)) ω) /
    (Fintype.card (Fin n → Bool) : ℝ)

/-- Root-inclusive cumulative posterior-variance area. -/
noncomputable def posteriorArea {n : ℕ}
    (F : (Fin n → Bool) → ℝ) (π : Observation n → Fin n) : ℝ :=
  ∑' t : ℕ, expectedPosteriorVarianceAt F π t

/-- The infimum of the areas of all legal one-coordinate policies. -/
noncomputable def policyAreaInf {n : ℕ}
    (F : (Fin n → Bool) → ℝ) : ℝ :=
  sInf {a : ℝ | ∃ π : Observation n → Fin n,
    LegalPolicy π ∧ posteriorArea F π = a}

/-- The harmonic number appearing in the obstruction. -/
noncomputable def harmonicNumber (m : ℕ) : ℝ :=
  Finset.sum (Finset.range m) (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ))

/-- The positive weight indexed by `j = 1, ..., m`. -/
noncomputable def harmonicWeight (m : ℕ) (j : Fin m) : ℝ :=
  1 / (((j.1 + 1 : ℕ) : ℝ) * harmonicNumber m)

/-- The shared-coordinate mixture, with every component returning the same sign. -/
noncomputable def sharedMixtureMean (m : ℕ) (ω : Fin 1 → Bool) : ℝ :=
  ∑ j : Fin m, harmonicWeight m j * rademacher (ω 0)

/-- The split product-occurrence mixture, with independent coordinates. -/
noncomputable def productMixtureMean (m : ℕ) (ω : Fin m → Bool) : ℝ :=
  ∑ j : Fin m, harmonicWeight m j * rademacher (ω j)

/--
The harmonic posterior-area obstruction for shared versus independently split
occurrences of depth-one Boolean components.
-/
noncomputable def harmonic_posterior_area_obstruction : Prop :=
  (∀ m : ℕ, 1 ≤ m →
    (∀ ω : Fin 1 → Bool,
      sharedMixtureMean m ω = rademacher (ω 0)) ∧
    policyAreaInf (sharedMixtureMean m) = 1 ∧
    policyAreaInf (productMixtureMean m) = 1 / harmonicNumber m ∧
    policyAreaInf (sharedMixtureMean m) /
        policyAreaInf (productMixtureMean m) = harmonicNumber m) ∧
  Filter.Tendsto harmonicNumber Filter.atTop Filter.atTop ∧
  (¬ ∃ C : ℝ, 0 ≤ C ∧
    ∀ m : ℕ, 1 ≤ m →
      policyAreaInf (sharedMixtureMean m) ≤
        C * policyAreaInf (productMixtureMean m)) ∧
  (∀ m : ℕ, 2 ≤ m →
    policyAreaInf (sharedMixtureMean m) ≠
      policyAreaInf (productMixtureMean m))

end MathlibPlus.Open
