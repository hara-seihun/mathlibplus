import Mathlib

namespace MathlibPlus.Open.Research

/-- Reindex the fibre permutations by a permutation of the base. -/
def coordinatePermute {Delta Lambda : Type*} (y : Equiv.Perm Delta) :
    (Delta → Equiv.Perm Lambda) ≃* (Delta → Equiv.Perm Lambda) :=
  { toFun := fun f d => f (y⁻¹ d)
    invFun := fun f d => f (y d)
    left_inv := by
      intro f
      funext d
      simp
    right_inv := by
      intro f
      funext d
      simp
    map_mul' := by
      intro f g
      funext d
      rfl }

/-- The base permutation action on the family of fibre permutations. -/
def coordinateAction {Delta Lambda : Type*}
    (Y : Subgroup (Equiv.Perm Delta)) :
    Y →* MulAut (Delta → Equiv.Perm Lambda) :=
  { toFun := fun y => coordinatePermute (y : Equiv.Perm Delta)
    map_one' := by
      ext f d
      rfl
    map_mul' := by
      intro y₁ y₂
      ext f d
      rfl }

/-- The imprimitive product wreath group `Sym(Lambda)^Delta ⋊ Y`. -/
abbrev FibreWreath (Delta Lambda : Type*)
    (Y : Subgroup (Equiv.Perm Delta)) :=
  SemidirectProduct (Delta → Equiv.Perm Lambda) Y (coordinateAction Y)

/-- The imprimitive action of the fibre wreath group on `Lambda × Delta`. -/
instance imprimitiveMulAction {Delta Lambda : Type*}
    (Y : Subgroup (Equiv.Perm Delta)) :
    MulAction (FibreWreath Delta Lambda Y) (Lambda × Delta) where
  smul w p :=
    (w.left (w.right.1 p.2) p.1, w.right.1 p.2)
  one_smul p := by
    rfl
  mul_smul w₁ w₂ p := by
    rw [SemidirectProduct.mul_def]
    change
      ((w₁.left * ((coordinateAction Y) w₁.right) w₂.left)
          ((w₁.right * w₂.right).1 p.2) p.1,
        (w₁.right * w₂.right).1 p.2) =
        (w₁.left (w₁.right.1 (w₂.right.1 p.2))
          (w₂.left (w₂.right.1 p.2) p.1),
          w₁.right.1 (w₂.right.1 p.2))
    apply Prod.ext
    · change
        (w₁.left ((w₁.right * w₂.right).1 p.2) *
            (((coordinateAction Y) w₁.right) w₂.left)
              ((w₁.right * w₂.right).1 p.2)) p.1 =
          w₁.left (w₁.right.1 (w₂.right.1 p.2))
            (w₂.left (w₂.right.1 p.2) p.1)
      simp [coordinateAction, coordinatePermute]
    · simp

/-- A subgroup is a regular copy of `A` when it is isomorphic to `A` and
acts freely and transitively on the stated carrier. -/
def IsRegularCopy (A G Ω : Type*) [Group A] [Group G] [SMul G Ω]
    (K : Subgroup G) : Prop :=
  Nonempty (K ≃* A) ∧
    ∀ x y : Ω, ∃! k : K, (k : G) • x = y

/-- Conjugacy of subgroups inside the ambient group. -/
def ConjugateSubgroups {G : Type*} [Group G]
    (K₁ K₂ : Subgroup G) : Prop :=
  ∃ g : G, ∀ x : G, x ∈ K₂ ↔ g * x * g⁻¹ ∈ K₁

/-- Relative full-fibre wreath lifting for finite permutation groups. -/
def relativeFullFibreWreathLifting
    (A H Delta Lambda : Type*)
    [Fintype A] [CommGroup A]
    [Fintype H] [Group H]
    [Fintype Delta] [Fintype Lambda]
    (hDelta : Fintype.card Delta = Fintype.card A)
    (hLambda : Fintype.card Lambda = Fintype.card H)
    (hcoprime : Nat.Coprime (Fintype.card A) (Fintype.card H))
    (Y : Subgroup (Equiv.Perm Delta)) : Prop :=
  (∀ K₁ K₂ : Subgroup Y,
      IsRegularCopy A Y Delta K₁ ∧ IsRegularCopy A Y Delta K₂ →
        ConjugateSubgroups K₁ K₂) →
    ∀ K₁ K₂ : Subgroup (FibreWreath Delta Lambda Y),
      IsRegularCopy (A × H) (FibreWreath Delta Lambda Y) (Lambda × Delta) K₁ ∧
          IsRegularCopy (A × H) (FibreWreath Delta Lambda Y) (Lambda × Delta) K₂ →
        ConjugateSubgroups K₁ K₂

end MathlibPlus.Open.Research
