import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain0901

/-! A rooted profile is indexed by a genuine integer partition and a part
value occurring in its multiset.  The multiset membership proof is a subtype,
so repeated equal parts do not create repeated coordinates. -/

private abbrev Partition (d : ℕ) := Nat.Partition d

private abbrev ProfileCoordinate (d : ℕ) :=
  Σ ρ : Partition d, {a : ℕ // a ∈ ρ.parts}

private def componentCount {d : ℕ} (ρ : Partition d) : ℕ := ρ.parts.card

private def splitParts {d : ℕ} (ρ : Partition d) (a : ℕ) : Multiset ℕ :=
  ρ.parts.erase a + {a + 1}

private def appendOneParts {d : ℕ} (ρ : Partition d) : Multiset ℕ :=
  ρ.parts + {1}

private def basisVector {d : ℕ} (ρ : Partition d) : Partition d → ℚ :=
  fun σ => if σ = ρ then 1 else 0

private def coordinateBoundary {d : ℕ} (c : ProfileCoordinate d) :
    Partition (d + 1) → ℚ :=
  fun σ =>
    (if σ.parts = splitParts c.1 c.2.1 then 1 else 0) -
      (if σ.parts = appendOneParts c.1 then 1 else 0)

private def incidenceMap (d : ℕ) :
    (ProfileCoordinate d → ℚ) →ₗ[ℚ] (Partition (d + 1) → ℚ) :=
  { toFun := fun α σ => ∑ c : ProfileCoordinate d, α c * coordinateBoundary c σ
    map_add' := by
      intro α β
      funext σ
      simp only [Pi.add_apply, add_mul]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro q α
      funext σ
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      simp only [RingHom.id_apply, mul_assoc] }

private def refinedMargin (d : ℕ) (α : ProfileCoordinate d → ℚ)
    (a ell : ℕ) : ℚ :=
  ∑ c : ProfileCoordinate d,
    (if c.2.1 = a ∧ componentCount c.1 = ell then 1 else 0) * α c

private def marginMap (d a ell : ℕ) :
    (ProfileCoordinate d → ℚ) →ₗ[ℚ] ℚ :=
  { toFun := fun α => refinedMargin d α a ell
    map_add' := by
      intro α β
      classical
      simp [refinedMargin, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro q α
      classical
      simp [refinedMargin, smul_eq_mul, Finset.mul_sum] }

private def tangentKernel (d : ℕ) : Submodule ℚ (ProfileCoordinate d → ℚ) :=
  LinearMap.ker (incidenceMap d) ⊓
    ⨅ a : ℕ, ⨅ ell : ℕ, LinearMap.ker (marginMap d a ell)

private def hasProfile {d : ℕ} (ρ : Partition d) (spec : ℕ → ℕ) : Prop :=
  ∀ n, ρ.parts.count n = spec n

private def profile421 (n : ℕ) : ℕ :=
  if n = 1 ∨ n = 2 ∨ n = 4 then 1 else 0

private def profile331 (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n = 3 then 2 else 0

private def profile322 (n : ℕ) : ℕ :=
  if n = 2 then 2 else if n = 3 then 1 else 0

private noncomputable def depthSevenGeneratorInt : ProfileCoordinate 7 → ℤ := by
  classical
  exact fun c =>
    if hasProfile c.1 profile421 ∧ c.2.1 = 1 then -1
    else if hasProfile c.1 profile421 ∧ c.2.1 = 2 then 1
    else if hasProfile c.1 profile331 ∧ c.2.1 = 1 then 1
    else if hasProfile c.1 profile331 ∧ c.2.1 = 3 then -1
    else if hasProfile c.1 profile322 ∧ c.2.1 = 2 then -1
    else if hasProfile c.1 profile322 ∧ c.2.1 = 3 then 1
    else 0

private noncomputable def depthSevenGenerator : ProfileCoordinate 7 → ℚ := by
  classical
  exact fun c => depthSevenGeneratorInt c

/-- Claim 27364: oriented rooted-profile coordinates are indexed by a
partition and a distinct occurring part value, not by occurrences. -/
def orientedRootedProfileCoordinates_claim27364 : Prop :=
  ∀ (d : ℕ) (ρ : Partition d) (a : ℕ),
    a ∈ ρ.parts →
      ∃! c : ProfileCoordinate d, c.1 = ρ ∧ c.2.1 = a

/-- Claim 27365: a selected part value gives the split-off-one oriented
incidence edge, with the signed endpoint difference. -/
def splitOffOnePartitionIncidence_claim27365 : Prop :=
  ∀ (d : ℕ) (ρ : Partition d) (a : ℕ) (ha : a ∈ ρ.parts),
    ∃ σ τ : Partition (d + 1),
      σ.parts = splitParts ρ a ∧
        τ.parts = appendOneParts ρ ∧
        coordinateBoundary ⟨ρ, ⟨a, ha⟩⟩ =
          (basisVector σ - basisVector τ)

/-- Claim 27366: refined margins sum the coefficients over partitions with a
selected part value and the prescribed total component count. -/
def refinedTangentMargins_claim27366 : Prop :=
  ∀ (d : ℕ) (α : ProfileCoordinate d → ℚ) (a ell : ℕ),
    refinedMargin d α a ell =
      ∑ ρ : Partition d,
        if h : a ∈ ρ.parts ∧ componentCount ρ = ell then
          α ⟨ρ, ⟨a, h.1⟩⟩
        else 0

/-- Claim 27367: the incidence kernel dimensions at depths one through seven
are the displayed tuple. -/
def incidenceCycleSpaceDimensions_claim27367 : Prop :=
  Module.finrank ℚ (LinearMap.ker (incidenceMap 1)) = 0 ∧
  Module.finrank ℚ (LinearMap.ker (incidenceMap 2)) = 0 ∧
  Module.finrank ℚ (LinearMap.ker (incidenceMap 3)) = 0 ∧
  Module.finrank ℚ (LinearMap.ker (incidenceMap 4)) = 1 ∧
  Module.finrank ℚ (LinearMap.ker (incidenceMap 5)) = 2 ∧
  Module.finrank ℚ (LinearMap.ker (incidenceMap 6)) = 5 ∧
  Module.finrank ℚ (LinearMap.ker (incidenceMap 7)) = 9

/-- Claim 27368: the incidence-and-margin kernel is zero through depth six and
one-dimensional at depth seven. -/
def tangentInvisibleIncidenceKernelDimensions_claim27368 : Prop :=
  (∀ d : ℕ, 1 ≤ d → d ≤ 6 → Module.finrank ℚ (tangentKernel d) = 0) ∧
    Module.finrank ℚ (tangentKernel 7) = 1

/-- Claim 27369: the displayed six-coordinate integral vector is a primitive
rational generator of the depth-seven tangent-invisible kernel. -/
def primitiveDepthSevenGenerator_claim27369 : Prop :=
  depthSevenGenerator ∈ tangentKernel 7 ∧
    (∀ α : ProfileCoordinate 7 → ℚ,
      α ∈ tangentKernel 7 → ∃ q : ℚ, α = q • depthSevenGenerator) ∧
    (∀ c : ProfileCoordinate 7,
      depthSevenGeneratorInt c ≠ 0 →
        depthSevenGeneratorInt c = 1 ∨ depthSevenGeneratorInt c = -1) ∧
    (∀ k : ℕ, 1 < k →
      ∃ c : ProfileCoordinate 7,
        depthSevenGeneratorInt c ≠ 0 ∧ ¬((k : ℤ) ∣ depthSevenGeneratorInt c))

/-- Claim 27371: every refined margin of the explicit depth-seven generator
vanishes; its two coordinates at each root size cancel. -/
def everyRefinedMarginOfGeneratorVanishes_claim27371 : Prop :=
  (∀ a ell : ℕ, refinedMargin 7 depthSevenGenerator a ell = 0) ∧
    (∀ c : ProfileCoordinate 7,
      hasProfile c.1 profile421 →
        ((c.2.1 = 1 → depthSevenGenerator c = -1) ∧
          (c.2.1 = 2 → depthSevenGenerator c = 1))) ∧
    (∀ c : ProfileCoordinate 7,
      hasProfile c.1 profile331 →
        ((c.2.1 = 1 → depthSevenGenerator c = 1) ∧
          (c.2.1 = 3 → depthSevenGenerator c = -1))) ∧
    (∀ c : ProfileCoordinate 7,
      hasProfile c.1 profile322 →
        ((c.2.1 = 2 → depthSevenGenerator c = -1) ∧
          (c.2.1 = 3 → depthSevenGenerator c = 1)))

/-- Claim 27372: the combined incidence-plus-margin map is injective through
selected-edge depth six. -/
def injectivityThroughSelectedEdgeDepthSix_claim27372 : Prop :=
  ∀ d : ℕ, 1 ≤ d → d ≤ 6 →
    ∀ α : ProfileCoordinate d → ℚ, α ∈ tangentKernel d → α = 0

end MathlibPlus.Open.NewResearch2.FormalizationDrain0901
