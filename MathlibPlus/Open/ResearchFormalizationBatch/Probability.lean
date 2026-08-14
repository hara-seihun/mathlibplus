import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Probability

open scoped BigOperators
open BigOperators

noncomputable section

variable {Ω T : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq T]

/-- A finite point-mass law. -/
def isProbability (p : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x : Ω, p x = 1)

def cellMass (p : Ω → ℝ) (C : Finset Ω) : ℝ :=
  Finset.sum C (fun x => p x)

def cellMean (p : Ω → ℝ) (C : Finset Ω) (Z : Ω → ℝ) : ℝ :=
  Finset.sum C (fun x => p x * Z x) / cellMass p C

def cellVariance (p : Ω → ℝ) (C : Finset Ω) (Z : Ω → ℝ) : ℝ :=
  Finset.sum C (fun x => p x * (Z x - cellMean p C Z) ^ 2) / cellMass p C

/-- The finite-experiment two-copy identity, with the conditioning factor present. -/
def finiteCellVarianceIdentity : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (C : Finset Ω) (Z : Ω → ℝ),
    isProbability p → 0 < cellMass p C →
      cellVariance p C Z =
        (1 / (2 * cellMass p C)) *
          (∑ x : Ω, ∑ y : Ω,
            if x ∈ C ∧ y ∈ C then
              p x * p y * (Z x - Z y) ^ 2
            else 0)

/-- The posterior law obtained by conditioning a finite point-mass law on a
    transcript value. -/
def posteriorWeight (p : Ω → ℝ) (H : Ω → T) (h : T) (q : ℝ) : Ω → ℝ :=
  fun x => if H x = h then p x / q else 0

def posteriorVariance (p : Ω → ℝ) (H : Ω → T) (h : T) (Z : Ω → ℝ) : ℝ :=
  let q := ∑ x : Ω, if H x = h then p x else 0
  cellVariance (posteriorWeight p H h q) Finset.univ Z

/-- Conditional iid two-copy identity for a complete transcript. -/
def posteriorIidTwoCopyIdentity : Prop :=
  ∀ (Ω T : Type*) [Fintype Ω] [DecidableEq Ω] [Fintype T] [DecidableEq T]
    (p : Ω → ℝ) (H : Ω → T) (h : T) (μ : Ω → ℝ),
    isProbability p →
    0 < (∑ x : Ω, if H x = h then p x else 0) →
      let q := ∑ x : Ω, if H x = h then p x else 0
      posteriorVariance p H h μ =
        (1 / 2) *
          ∑ x : Ω, ∑ y : Ω,
            posteriorWeight p H h q x * posteriorWeight p H h q y *
              (μ x - μ y) ^ 2

/-- Incidence mass of a finite family of nonempty supports.  A finite index type
    represents the paths of a finite multiset, including repeated supports. -/
def incidenceMass {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (e : ι → Finset V) (a : ι → ℝ) (v : V) : ℝ :=
  ∑ p : ι, if v ∈ e p then a p else 0

def rankConditions {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    {n : ℕ} (e : ι → Finset V) (a : ι → ℝ)
    (π : V ≃ Fin n) (rank : ι → ℕ) : Prop :=
  (∀ u v : V, π u < π v → incidenceMass e a u ≥ incidenceMass e a v) ∧
  (∀ p : ι,
    (e p).Nonempty ∧
      (∃ v ∈ e p, rank p = (π v).val + 1) ∧
      (∀ v ∈ e p, (π v).val + 1 ≤ rank p))

/-- The static path inequality with the explicit last-coordinate ranks. -/
def staticPathInequality : Prop :=
  ∀ (V ι : Type*) [Fintype V] [DecidableEq V] [Fintype ι]
    (k n : ℕ) (e : ι → Finset V) (a : ι → ℝ)
    (π : V ≃ Fin n) (rank : ι → ℕ),
    (∀ p : ι, 0 ≤ a p) →
    (∀ p : ι, (e p).Nonempty) →
    (∀ p : ι, (e p).card ≤ k) →
    rankConditions e a π rank →
      (∑ p : ι, a p ^ 2 * (rank p : ℝ)) ≤
          (∑ p : ι, a p) * (∑ p : ι, (e p).card * a p) ∧
      (∑ p : ι, a p) * (∑ p : ι, (e p).card * a p) ≤
          (k : ℝ) * (∑ p : ι, a p) ^ 2

/-- A single path of size `k` realizes equality in the final static bound. -/
def staticPathSharpness : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ A : ℝ, 0 ≤ A →
    let e : Unit → Finset (Fin k) := fun _ => Finset.univ
    let a : Unit → ℝ := fun _ => A
    let π : Fin k ≃ Fin k := Equiv.refl _
    let rank : Unit → ℕ := fun _ => k
    (rankConditions e a π rank) ∧
      (∑ p : Unit, a p ^ 2 * (rank p : ℝ)) = (k : ℝ) * A ^ 2

/-- The concrete three-sign witness law, with uniform mass inside every
    Hamming-weight class. -/
abbrev SignΩ := Fin 3 → Bool

def signCount (ω : SignΩ) : ℕ :=
  (Finset.filter (fun i : Fin 3 => ω i = true) Finset.univ).card

def signClassMass (k : ℕ) : ℝ :=
  if k = 0 then 2 / 5 else
    if k = 1 then 1 / 10 else
      if k = 2 then 1 / 10 else
        if k = 3 then 2 / 5 else 0

def signLaw (ω : SignΩ) : ℝ :=
  signClassMass (signCount ω) /
    ((Finset.filter (fun ω' : SignΩ => signCount ω' = signCount ω) Finset.univ).card : ℝ)

def signValue (b : Bool) : ℝ := if b then 1 else -1

def signOutput (ω : SignΩ) : ℝ :=
  (∑ i : Fin 3, signValue (ω i)) / 3

/-- The exchangeable class law and the specified output. -/
def threeSignWitnessSetup : Prop :=
  (∑ ω : SignΩ, signLaw ω = 1) ∧
  (∀ ω ω' : SignΩ, signCount ω = signCount ω' → signLaw ω = signLaw ω') ∧
  (∀ σ : Equiv.Perm (Fin 3), ∀ ω : SignΩ,
    signLaw (ω ∘ σ) = signLaw ω) ∧
  (∑ ω : SignΩ, (if signCount ω = 0 then signLaw ω else 0)) = 2 / 5 ∧
  (∑ ω : SignΩ, (if signCount ω = 1 then signLaw ω else 0)) = 1 / 10 ∧
  (∑ ω : SignΩ, (if signCount ω = 2 then signLaw ω else 0)) = 1 / 10 ∧
  (∑ ω : SignΩ, (if signCount ω = 3 then signLaw ω else 0)) = 2 / 5

def signCell (m : Fin 3) (r : Fin m.val → Bool) : Finset SignΩ :=
  Finset.filter
    (fun ω : SignΩ =>
      ∀ i : Fin m.val,
        ω ⟨i.val, Nat.lt_trans i.isLt m.isLt⟩ = r i)
    Finset.univ

def averagedSignVarianceLayer (m : Fin 3) : ℝ :=
  ∑ r : Fin m.val → Bool,
    cellMass signLaw (signCell m r) *
      cellVariance signLaw (signCell m r) signOutput

/-- The exact averaged conditional-variance layers for zero, one, and two
    revealed coordinates. -/
def threeSignVarianceLayers : Prop :=
  averagedSignVarianceLayer ⟨0, by decide⟩ = 37 / 45 ∧
  averagedSignVarianceLayer ⟨1, by decide⟩ = 296 / 2025 ∧
  averagedSignVarianceLayer ⟨2, by decide⟩ = 74 / 1755 ∧
  averagedSignVarianceLayer ⟨0, by decide⟩ +
      averagedSignVarianceLayer ⟨1, by decide⟩ +
      averagedSignVarianceLayer ⟨2, by decide⟩ = 26603 / 26325 ∧
  1 < averagedSignVarianceLayer ⟨0, by decide⟩ +
      averagedSignVarianceLayer ⟨1, by decide⟩ +
      averagedSignVarianceLayer ⟨2, by decide⟩

end
end MathlibPlus.Open.ResearchFormalizationBatch.Probability
