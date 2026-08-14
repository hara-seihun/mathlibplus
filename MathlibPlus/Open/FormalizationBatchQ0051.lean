import Mathlib

namespace MathlibPlus.Open.FormalizationBatchQ0051

/-- A block map on `F × B`, written in the fibre/base coordinates used by the
permutation-holonomy criterion. -/
structure WreathChart (F B : Type*) where
  fibre : B → Equiv.Perm F
  base : Equiv.Perm B

/-- The action of a block map on the underlying points. -/
def chartApply {F B : Type*} (u : WreathChart F B) (x : F × B) : F × B :=
  (u.fibre x.2 x.1, u.base x.2)

/-- Multiplication in the fibre/base presentation of a wreath product. -/
def chartMul {F B : Type*} (u v : WreathChart F B) : WreathChart F B :=
  { fibre := fun b => u.fibre (v.base b) * v.fibre b
    base := u.base * v.base }

/-- The identity chart. -/
def chartOne (F B : Type*) : WreathChart F B :=
  { fibre := fun _ => Equiv.refl F
    base := Equiv.refl B }

/-- Inversion in the fibre/base presentation. -/
def chartInv {F B : Type*} (u : WreathChart F B) : WreathChart F B :=
  { fibre := fun b => (u.fibre (u.base.symm b)).symm
    base := u.base.symm }

/-- The subgroup conditions for a set of wreath charts.  They avoid hiding the
wreath-product carrier behind an unmentioned representation. -/
def IsChartSubgroup {F B : Type*} (K : Set (WreathChart F B)) : Prop :=
  chartOne F B ∈ K ∧
    (∀ u ∈ K, ∀ v ∈ K, chartMul u v ∈ K) ∧
    (∀ u ∈ K, chartInv u ∈ K)

/-- The orbit of a point under a set of block charts. -/
def chartOrbit {F B : Type*} (K : Set (WreathChart F B))
    (x : F × B) : Set (F × B) :=
  {y | ∃ u, u ∈ K ∧ chartApply u x = y}

/-- The projected orbit in the block coordinate. -/
def projectedOrbit {F B : Type*} (K : Set (WreathChart F B))
    (b : B) : Set B :=
  {c | ∃ u, u ∈ K ∧ u.base b = c}

/-- Root-stabilizer holonomy at a block root. -/
def rootHolonomy {F B : Type*} (K : Set (WreathChart F B))
    (r : B) : Set (Equiv.Perm F) :=
  {h | ∃ u, u ∈ K ∧ u.base r = r ∧ h = u.fibre r}

/-- An orbit of the displayed permutation set on the fibre. -/
def holonomyOrbit {F : Type*} (L : Set (Equiv.Perm F)) (x : F) : Set F :=
  {y | ∃ h, h ∈ L ∧ h x = y}

/-- `∏ Sym(P)` for the holonomy-orbit partition: every orbit is fixed
individually, rather than merely permuted. -/
def pointwiseOrbitPartitionStabilizer {F : Type*}
    (L : Set (Equiv.Perm F)) : Set (Equiv.Perm F) :=
  {σ | ∀ x y, y ∈ holonomyOrbit L x ↔ σ y ∈ holonomyOrbit L x}

/-- A family of root-to-fibre path maps, expressed by actual elements of `K`.
Thus the maps are not unconstrained auxiliary witnesses. -/
def IsRootPathFamily {F B : Type*} (K : Set (WreathChart F B))
    (r : B) (τ : B → Equiv.Perm F) : Prop :=
  ∀ b, b ∈ projectedOrbit K r →
    ∃ u, u ∈ K ∧ u.base r = b ∧ τ b = u.fibre r

/-- The condition on one projected component in the unified criterion. -/
def componentHolonomyCondition {F B : Type*}
    (K : Set (WreathChart F B)) (f : WreathChart F B)
    (r : B) (τ : B → Equiv.Perm F) : Prop :=
  Set.image f.base (projectedOrbit K r) = projectedOrbit K r ∧
    ∀ b, b ∈ projectedOrbit K r →
      (τ (f.base b)).symm * f.fibre b * τ b ∈
        pointwiseOrbitPartitionStabilizer (rootHolonomy K r)

/-- Setwise fixation of every `K`-orbit on `Ω = F × B`. -/
def fixesEveryChartOrbit {F B : Type*}
    (K : Set (WreathChart F B)) (f : WreathChart F B) : Prop :=
  ∀ x, chartOrbit K (chartApply f x) = chartOrbit K x

/-- Claim 16148: the permutation-holonomy orbit criterion, including the
root/path-choice independence expressed by quantifying over every valid path
family. -/
def claim16148 : Prop :=
  ∀ {F B : Type*} (K : Set (WreathChart F B)) (f : WreathChart F B),
    IsChartSubgroup K →
      (∀ r : B, ∃ τ : B → Equiv.Perm F, IsRootPathFamily K r τ) ∧
      (fixesEveryChartOrbit K f ↔
        ∀ r : B, ∀ τ : B → Equiv.Perm F,
          IsRootPathFamily K r τ → componentHolonomyCondition K f r τ) ∧
      (∀ r₁ r₂ : B, ∀ τ₁ τ₂ : B → Equiv.Perm F,
        projectedOrbit K r₁ = projectedOrbit K r₂ →
        IsRootPathFamily K r₁ τ₁ → IsRootPathFamily K r₂ τ₂ →
          (componentHolonomyCondition K f r₁ τ₁ ↔
            componentHolonomyCondition K f r₂ τ₂))

end MathlibPlus.Open.FormalizationBatchQ0051
