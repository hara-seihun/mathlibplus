import Mathlib

namespace MathlibPlus.Open.GraphTheory.R0943

/-- Left translation as a permutation of a group. -/
def leftTranslation {G : Type*} [Group G] (a : G) : Equiv.Perm G :=
  { toFun := fun x => a * x
    invFun := fun x => a⁻¹ * x
    left_inv := by intro x; simp
    right_inv := by intro x; simp }

/-- The normalized relative derivatives used in the affine-fibre claims. -/
def normalizedRelativeDerivative {G : Type*} [Group G]
    (f : Equiv.Perm G) (a : G) : Equiv.Perm G :=
  leftTranslation (f a)⁻¹ * f * leftTranslation a * f⁻¹

def normalizedRelativeDerivativeGroup {G : Type*} [Group G]
    (f : Equiv.Perm G) : Subgroup (Equiv.Perm G) :=
  Subgroup.closure (Set.range (normalizedRelativeDerivative f))

def derivativeInvariantSet {G : Type*} [Group G]
    (f : Equiv.Perm G) (S : Set G) : Prop :=
  ∀ g ∈ normalizedRelativeDerivativeGroup f, g '' S = S

/-- R-0943.1: over an odd base, every normalized identity-base affine fibre
    map fixes every set invariant under its relative derivatives. -/
def r0943_oddIdentityBaseAffine : Prop :=
  ∀ {V H : Type*} [Fintype V] [AddCommGroup V]
      [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      [Fintype H] [Group H],
    Odd (Fintype.card H) →
    ∀ (A : H → (V ≃+ V)) (c : H → V),
      A 1 = AddEquiv.refl V → c 1 = 0 →
      let G := Multiplicative V × H
    ∀ f : Equiv.Perm G,
        (∀ v h, f (.ofAdd v, h) = (.ofAdd (A h v + c h), h)) →
        ∀ S : Set G, derivativeInvariantSet f S → f '' S = S

/-- R-0943.3: the even-order base-two example has trivial relative-derivative
    group but the indicated normalized affine map is not orbit-fixing. -/
def r0943_evenOrderCounterexample : Prop :=
  let G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  ∃ f : Equiv.Perm G,
    (∀ v b : Multiplicative (ZMod 2), f (v, b) = (v * b, b)) ∧
      normalizedRelativeDerivativeGroup f = ⊥ ∧
      ∃ v b : Multiplicative (ZMod 2), f (v, b) ≠ (v, b)

/-- The additive Cayley transport used for the elementary-two residuals. -/
def additiveCayleyTransport {G : Type*} [Sub G]
    (S T : Set G) (e : Equiv G G) : Prop :=
  ∀ x y, y - x ∈ S ↔ e y - e x ∈ T

def additiveAutomorphismShadow {G : Type*} [AddGroup G]
    (S T : Set G) : Prop :=
  ∃ α : G ≃+ G, α '' S = T

def identityBaseAffineOverNine {V : Type*} [AddGroup V]
    (f : Equiv (V × ZMod 9) (V × ZMod 9)) : Prop :=
  ∃ (A : ZMod 9 → (V ≃+ V)) (c : ZMod 9 → V),
    A 0 = AddEquiv.refl V ∧ c 0 = 0 ∧
      ∀ v i, f (v, i) = (A i v + c i, i)

/-- R-0943.4: on the three elementary-two times C₉ candidates, an
    identity-base affine fibre map cannot itself be a CI or DCI witness. -/
def r0943_elementaryTwoAffineResiduals : Prop :=
  ∀ r : ℕ, r = 3 ∨ r = 4 ∨ r = 5 →
    let V := Fin r → ZMod 2
    let G := V × ZMod 9
    ∀ f : Equiv G G, identityBaseAffineOverNine f →
      ¬ ∃ S T : Set G,
        additiveCayleyTransport S T f ∧
          ¬ additiveAutomorphismShadow S T

/-- A loopless symmetric five-colouring transport on a finite group. -/
def symmetricFiveColorTransport {A : Type*} [Group A]
    (c d : A → Fin 5) (e : Equiv A A) : Prop :=
  ∀ x y k, (c (x⁻¹ * y) = k) ↔ (d ((e x)⁻¹ * e y) = k)

def symmetricFiveColorDefect {A : Type*} [Group A]
    (c d : A → Fin 5) : Prop :=
  c 1 = 0 ∧ d 1 = 0 ∧
    (∀ a, c a = c a⁻¹) ∧ (∀ a, d a = d a⁻¹) ∧
    ∃ e : Equiv A A, symmetricFiveColorTransport c d e ∧
      ¬ ∃ α : A ≃* A, ∀ a, c a = d (α a)

abbrev V4 := Fin 2 → ZMod 2
abbrev V4Group := Multiplicative V4

def affineV4ProfileInvariant : Prop :=
  Fintype.card (V4 × (V4 ≃+ V4)) = 24 ∧
    Fintype.card (V4 ≃+ V4) = 6 ∧
    ∀ (F G : Set V4),
      0 ∉ F → 0 ∉ G →
      Set.ncard F = Set.ncard G →
      ∃ α : V4 ≃+ V4, α '' F = G

/-- R-0943.5: the exact four-point section invariant attached to the
    definition of symmetric five-colour CI. -/
def symmetricFiveColorCI {A : Type*} [Fintype A] [Group A]
    (_hOdd : Odd (Fintype.card A)) : Prop :=
  (∀ (c d : A → Fin 5),
    c 1 = 0 → d 1 = 0 →
    (∀ a, c a = c a⁻¹) → (∀ a, d a = d a⁻¹) →
    ∀ e : Equiv A A, symmetricFiveColorTransport c d e →
      ∃ α : A ≃* A, ∀ a, c a = d (α a)) ∧
  affineV4ProfileInvariant

/-- The centre-kernel projection data for the quaternion lift. -/
def quaternionProjectionData (π : QuaternionGroup 2 →* V4Group) : Prop :=
  Function.Surjective π ∧
    (∀ q : QuaternionGroup 2,
      π q = 1 ↔ q ∈ (Subgroup.center (QuaternionGroup 2) : Set (QuaternionGroup 2)))

noncomputable def quaternionLiftedSet {A : Type*} [Group A]
    (π : QuaternionGroup 2 →* V4Group) (F : Fin 5 → Set V4Group)
    (c : A → Fin 5) : Set (A × QuaternionGroup 2) :=
  {g | g.1 ≠ 1 ∧ π g.2 ∈ F (c g.1)}

/-- R-0943.8: a nonautomorphic symmetric five-colour pair lifts through the
    central quotient of Q₈ to a nonautomorphic ordinary inverse-closed pair. -/
def r0943_fiveColorDefectLifts : Prop :=
  ∀ {A : Type*} [Fintype A] [Group A],
    ∀ (c d : A → Fin 5), symmetricFiveColorDefect c d →
      ∀ (π : QuaternionGroup 2 →* V4Group), quaternionProjectionData π →
        ∀ (F : Fin 5 → Set V4Group),
          (∀ k : Fin 5, Set.ncard (F k) = k) →
          let S := quaternionLiftedSet π F c
          let T := quaternionLiftedSet π F d
          (∀ g, g ∈ S ↔ g⁻¹ ∈ S) ∧
            (∀ g, g ∈ T ↔ g⁻¹ ∈ T) ∧
            (∃ e : Equiv (A × QuaternionGroup 2) (A × QuaternionGroup 2),
              ∀ x y, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
            (∀ a : A, a ≠ 1 →
              Set.ncard {q : QuaternionGroup 2 | π q ∈ F (c a)} =
                2 * (c a : ℕ)) ∧
            (∀ a : A, a ≠ 1 →
              Set.ncard {q : QuaternionGroup 2 | π q ∈ F (d a)} =
                2 * (d a : ℕ)) ∧
            ¬ ∃ α : (A × QuaternionGroup 2) ≃* (A × QuaternionGroup 2),
              α '' S = T

end MathlibPlus.Open.GraphTheory.R0943
