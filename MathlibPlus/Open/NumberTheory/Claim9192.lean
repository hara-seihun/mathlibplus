import Mathlib

namespace MathlibPlus.Open.NumberTheory.Claim9192

open scoped BigOperators

noncomputable section

/-- The complex roots of the minimal polynomial, regarded as a finite set. -/
def conjugateRoots (α : ℂ) : Finset ℂ :=
  ((minpoly ℚ α).map (algebraMap ℚ ℂ)).roots.toFinset

/-- The exterior conjugates, namely those of modulus strictly larger than one. -/
def exteriorRoots (α : ℂ) : Finset ℂ :=
  (conjugateRoots α).filter (fun z => 1 < ‖z‖)

/-- The Galois orbit of the exterior set under automorphisms of `ℂ` over `ℚ`. -/
def exteriorOrbit (α : ℂ) : Set (Finset ℂ) :=
  {B | ∃ σ : ℂ ≃ₐ[ℚ] ℂ, B = (exteriorRoots α).image (fun z => σ z)}

/-- Every conjugate occurs in exactly one block of the exterior-set orbit. -/
def replicationOne (α : ℂ) : Prop :=
  ∀ z ∈ conjugateRoots α, ∃! B : Finset ℂ,
    B ∈ exteriorOrbit α ∧ z ∈ B

/-- The product of the exterior conjugates. -/
def exteriorProduct (α : ℂ) : ℂ :=
  Finset.prod (exteriorRoots α) (fun z => z)

/-- Mahler measure, written from the conjugates of an algebraic number. -/
def mahlerMeasure (α : ℂ) : ℝ :=
  Finset.prod (conjugateRoots α) (fun z => max (1 : ℝ) ‖z‖)

/-- Non-cyclotomic means that the number is not a root of unity. -/
def nonCyclotomic (α : ℂ) : Prop :=
  ¬ ∃ n : ℕ, 0 < n ∧ α ^ n = 1

/-- The hypotheses on the algebraic integer in Claim 9192. -/
def admissible (α : ℂ) : Prop :=
  IsIntegral ℤ α ∧
    (minpoly ℚ α).Monic ∧
    Irreducible (minpoly ℚ α) ∧
    (minpoly ℚ α).reverse = minpoly ℚ α ∧
    nonCyclotomic α ∧
    replicationOne α

/-- A Pisot number: a real algebraic integer greater than one whose other
conjugates are strictly inside the unit disk. -/
def PisotNumber (β : ℝ) : Prop :=
  1 < β ∧
    IsIntegral ℤ β ∧
    ∀ z ∈ conjugateRoots (β : ℂ), z ≠ (β : ℂ) → ‖z‖ < 1

/-- A Salem number: a real algebraic unit greater than one whose other
conjugates lie in the closed unit disk and with one on its boundary. -/
def SalemNumber (β : ℝ) : Prop :=
  1 < β ∧
    IsIntegral ℤ β ∧
    IsIntegral ℤ β⁻¹ ∧
    (∀ z ∈ conjugateRoots (β : ℂ), z ≠ (β : ℂ) → ‖z‖ ≤ 1) ∧
    ∃ z ∈ conjugateRoots (β : ℂ), z ≠ (β : ℂ) ∧ ‖z‖ = 1

/-- Every admissible reciprocal algebraic integer with replication-one
exterior orbit maps, without a degree or exterior-cardinality restriction, to
 a Pisot or Salem number with the same Mahler measure. -/
def losslessDegreeUniformReduction : Prop :=
  ∀ α : ℂ,
    admissible α →
      ∃ β : ℝ,
        β = mahlerMeasure α ∧
          ((β : ℂ) = exteriorProduct α ∨
            (β : ℂ) = -exteriorProduct α) ∧
          (PisotNumber β ∨ SalemNumber β) ∧
          mahlerMeasure (β : ℂ) = mahlerMeasure α

end

end MathlibPlus.Open.NumberTheory.Claim9192
