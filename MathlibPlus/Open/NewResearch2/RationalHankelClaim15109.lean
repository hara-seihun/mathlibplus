import MathlibPlus.Open.NewResearch2.RationalHankel15108

open scoped BigOperators
open Polynomial
open Set

namespace MathlibPlus.Open.NewResearch2.RationalHankelClaim15109

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankelStructure
open MathlibPlus.Open.NewResearch2.RationalHankel15108

/-- A contour is represented by its continuous simple closed boundary and its
open bounded interior.  Thus contour groupings below are not arbitrary set
partitions. -/
structure SimpleContour where
  curve : ℝ → ℂ
  continuous_curve : ContinuousOn curve (Set.Icc (0 : ℝ) 1)
  closed_loop : curve 0 = curve 1
  simple_interior : Set.InjOn curve (Set.Ioo (0 : ℝ) 1)
  interior : Set ℂ
  interior_open : IsOpen interior
  interior_bounded : Bornology.IsBounded interior
  boundary_eq : frontier interior = curve '' Set.Icc (0 : ℝ) 1

/-- The normalized linear factor with root `zeta`. -/
def normalizedRootFactor (zeta : ℂ) : Polynomial ℂ :=
  1 - Polynomial.C (zeta⁻¹) * Polynomial.X

/-- A finite shell profile retains the shell's own multiplicities.  They may
be strictly smaller than the multiplicity of the same root in `G`, so partial
repeated-root divisors are included. -/
def shellRootProfile {J : ℕ}
    (S G : Polynomial ℂ) (zeta : Fin J → ℂ) (mu : Fin J → ℕ) : Prop :=
  S ≠ 0 ∧
    S.coeff 0 = 1 ∧
      S ∣ G ∧
        (∀ j : Fin J, zeta j ≠ 0 ∧ 0 < mu j) ∧
          (∀ i j : Fin J, i ≠ j → zeta i ≠ zeta j) ∧
            S = ∏ j : Fin J, normalizedRootFactor (zeta j) ^ mu j

/-- A mixed shell contains at least two distinct root nodes in its own finite
profile. -/
def mixedShell (S G : Polynomial ℂ) : Prop :=
  ∃ (J : ℕ) (zeta : Fin J → ℂ) (mu : Fin J → ℕ),
    shellRootProfile S G zeta mu ∧
      ∃ i j : Fin J, i ≠ j

/-- A confluent shell has a repeated node in its own profile. -/
def confluentShell (S G : Polynomial ℂ) : Prop :=
  ∃ (J : ℕ) (zeta : Fin J → ℂ) (mu : Fin J → ℕ),
    shellRootProfile S G zeta mu ∧
      ∃ j : Fin J, 1 < mu j

/-- The shell factor contributed by one contour or one equal-modulus class. -/
noncomputable def groupedShell {J a : ℕ}
    (zeta : Fin J → ℂ) (mu : Fin J → ℕ)
    (assignment : Fin J → Fin a) (i : Fin a) : Polynomial ℂ :=
  ∏ j : Fin J,
    if assignment j = i then
      normalizedRootFactor (zeta j) ^ mu j
    else 1

/-- Roots assigned to pairwise disjoint contour interiors. -/
def disjointContourGrouping {J a : ℕ}
    (zeta : Fin J → ℂ) (assignment : Fin J → Fin a)
    (contours : Fin a → SimpleContour) : Prop :=
  (∀ u v : Fin a, u ≠ v →
    Disjoint (contours u).interior (contours v).interior) ∧
    (∀ j : Fin J, zeta j ∈ (contours (assignment j)).interior)

/-- Roots assigned exactly by equality of modulus. -/
def equalModulusGrouping {J a : ℕ}
    (zeta : Fin J → ℂ) (assignment : Fin J → Fin a) : Prop :=
  ∀ i j : Fin J,
    assignment i = assignment j ↔ ‖zeta i‖ = ‖zeta j‖

/-- A valid grouping partitions the shell factor itself and gives each class
an exact divisor of the ambient common divisor. -/
def groupingFactorization {J a : ℕ}
    (S G : Polynomial ℂ) (zeta : Fin J → ℂ) (mu : Fin J → ℕ)
    (assignment : Fin J → Fin a) : Prop :=
  S = ∏ i : Fin a, groupedShell zeta mu assignment i ∧
    (∀ i : Fin a, groupedShell zeta mu assignment i ∣ G)

/-- Exact removability is the common-divisor criterion, not a generic
quotient or an unconstrained replacement function. -/
def exactlyRemovable {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q S : Polynomial ℂ) (G : Polynomial ℂ) : Prop :=
  S ∣ G ∧
    MathlibPlus.Open.NewResearch2.RationalHankel15108.divisionLeavesRationalFunctionUnchanged
      P Q S

/-- Claim 15109: every finite mixed or confluent shell of the exact common
Froissart divisor is captured by its own root/multiplicity profile.  Any
arbitrary disjoint contour grouping of that profile, and the equal-modulus
partition of it, produces exact removable factors, with no positivity,
minor-sign, simple-pole, or phase-separation premise. -/
def claim_15109 : Prop :=
  ∀ (d : ℕ) (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ),
    properVectorRationalModel P Q →
      let G := commonFroissartDivisor P Q
      ∀ S : Polynomial ℂ,
        (mixedShell S G ∨ confluentShell S G) →
          ∃ (J : ℕ) (zeta : Fin J → ℂ) (mu : Fin J → ℕ),
            shellRootProfile S G zeta mu ∧
              exactlyRemovable P Q S G ∧
              (∀ (a : ℕ) (contours : Fin a → SimpleContour)
                (assignment : Fin J → Fin a),
                disjointContourGrouping zeta assignment contours →
                  groupingFactorization S G zeta mu assignment ∧
                    (∀ i : Fin a,
                      exactlyRemovable P Q
                        (groupedShell zeta mu assignment i) G)) ∧
              (∀ (a : ℕ) (assignment : Fin J → Fin a),
                equalModulusGrouping zeta assignment →
                  groupingFactorization S G zeta mu assignment ∧
                    (∀ i : Fin a,
                      exactlyRemovable P Q
                        (groupedShell zeta mu assignment i) G))

end

end MathlibPlus.Open.NewResearch2.RationalHankelClaim15109
