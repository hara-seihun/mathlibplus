import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim29206

noncomputable section

private abbrev BooleanBase (d : ℕ) (B : Type*) [AddCommGroup B] :=
  (Fin (d - 1) → ZMod 2) × B

private abbrev BooleanLift (d : ℕ) (B : Type*) [AddCommGroup B] :=
  BooleanBase d B × ZMod 2

private def canonicalRegularCopy {G : Type*} [AddCommGroup G] :
    Subgroup (Equiv.Perm G) :=
  Subgroup.closure (Set.range (fun a : G => Equiv.addRight a))

private def globalSwap {d : ℕ} {B : Type*} [AddCommGroup B] :
    Equiv.Perm (BooleanLift d B) :=
  Equiv.addRight (0, 1)

private def regularSubgroup {G : Type*}
    (R : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ x y : G, ∃! r : R, (r : Equiv.Perm G) x = y

private def block {d : ℕ} {B : Type*} [AddCommGroup B]
    (h : BooleanBase d B) : Set (BooleanLift d B) :=
  {x | x.1 = h}

private def preservesBlocks {d : ℕ} {B : Type*} [AddCommGroup B]
    (R : Subgroup (Equiv.Perm (BooleanLift d B))) : Prop :=
  ∀ r : R, ∀ h : BooleanBase d B, ∃ k : BooleanBase d B,
    (r : Equiv.Perm (BooleanLift d B)) '' block h = block k

private def blockProjection {d : ℕ} {B : Type*} [AddCommGroup B]
    (x : BooleanLift d B) : BooleanBase d B := x.1

/-- The image of an actual permutation subgroup on the actual two-point
quotient, not an abstract quotient permutation group. -/
private def actualQuotientImage {d : ℕ} {B : Type*} [AddCommGroup B]
    (R : Subgroup (Equiv.Perm (BooleanLift d B))) :
    Set (Equiv.Perm (BooleanBase d B)) :=
  {q | ∃ r : Equiv.Perm (BooleanLift d B), r ∈ R ∧
    ∀ x, q (blockProjection x) = blockProjection (r x)}

private def normalizedBooleanSwitching {d : ℕ} {B : Type*} [AddCommGroup B]
    (b : BooleanBase d B → ZMod 2)
    (f : Equiv.Perm (BooleanLift d B)) : Prop :=
  b 0 = 0 ∧ ∀ (h : BooleanBase d B) (e : ZMod 2),
    f (h, e) = (h, e + b h)

private def normalizedRelativeDerivative {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) (x : G) : Equiv.Perm G :=
  (((Equiv.addRight x).trans f).trans
    (Equiv.subRight (f x))).trans f.symm

private def derivativeGroup {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) : Subgroup (Equiv.Perm G) :=
  Subgroup.closure (Set.range (normalizedRelativeDerivative f))

private def derivativeOrbit {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) (x : G) : Set G :=
  MulAction.orbit (derivativeGroup f) x

private def derivativeInvariant {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) (S : Set G) : Prop :=
  ∀ x : G, ∀ p : derivativeGroup f,
    x ∈ S ↔ p.1 x ∈ S

private def connectionSet {G : Type*} [AddCommGroup G]
    (S : Set G) : Prop :=
  0 ∉ S

private def cayleyAutomorphism {G : Type*} [AddCommGroup G]
    (S : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y : G, y - x ∈ S ↔ f y - f x ∈ S

private def carriesCayleyConnectionSet {G : Type*} [AddCommGroup G]
    (S : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y : G, y - x ∈ S ↔ f y - f x ∈ Set.image f S

private def conjugatesCopies {G : Type*}
    (f : Equiv.Perm G)
    (R T : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ r : Equiv.Perm G, r ∈ R ↔ f * r * f⁻¹ ∈ T

/-- The exact aligned interface after choosing the common two-point quotient
coordinates.  `R` is the concrete regular copy in the presentation
coordinates; `T` is the actual second copy inside the actual Cayley
automorphism group.  The quotient image is formed from the actual block
fibres, and `f` is required to be the normalized presentation map, rather
than an unrelated permutation conjugating abstract subgroups. -/
private def alignedRegularLift {d : ℕ} {B : Type*}
    [AddCommGroup B] [Fintype B]
    (S : Set (BooleanLift d B))
    (R T : Subgroup (Equiv.Perm (BooleanLift d B)))
    (b : BooleanBase d B → ZMod 2)
    (f : Equiv.Perm (BooleanLift d B)) : Prop :=
  R = canonicalRegularCopy ∧
    regularSubgroup R ∧
    regularSubgroup T ∧
    Nonempty (R ≃* Multiplicative (BooleanLift d B)) ∧
    Nonempty (T ≃* Multiplicative (BooleanLift d B)) ∧
    globalSwap ∈ R ∧
    globalSwap ∈ T ∧
    (∀ r : Equiv.Perm (BooleanLift d B), r ∈ R →
      cayleyAutomorphism S r) ∧
    (∀ t : Equiv.Perm (BooleanLift d B), t ∈ T →
      cayleyAutomorphism S t) ∧
    preservesBlocks R ∧
    preservesBlocks T ∧
    actualQuotientImage R = actualQuotientImage T ∧
    normalizedBooleanSwitching b f ∧
    (∀ h : BooleanBase d B, f '' block h = block h) ∧
    carriesCayleyConnectionSet S f ∧
    conjugatesCopies f R T

/-- Claim 29206.  For the normalized Boolean presentation map supplied by
an actual aligned regular lift, a character shear has the same image on every
relative-derivative orbit.  Consequently it agrees with the presentation map
on every identity-free connection set invariant under those orbits; the
composite `f_b` followed by the inverse character shear is a Cayley
(graph/digraph) automorphism and still conjugates the two actual regular
copies. -/
def claim29206 : Prop :=
  ∀ (d : ℕ) (B : Type*) [AddCommGroup B] [Fintype B],
    0 < d →
    Odd (Fintype.card B) →
    ∀ (S : Set (BooleanLift d B))
      (R T : Subgroup (Equiv.Perm (BooleanLift d B)))
      (b : BooleanBase d B → ZMod 2)
      (f : Equiv.Perm (BooleanLift d B)),
      alignedRegularLift S R T b f →
      ∃ χ : BooleanBase d B →+ ZMod 2,
        ∃ α : (BooleanLift d B) ≃+ (BooleanLift d B),
          (∀ h : BooleanBase d B, ∀ e : ZMod 2,
            α (h, e) = (h, e + χ h)) ∧
          (∀ x : BooleanLift d B,
            Set.image α.toEquiv (derivativeOrbit f x) =
              Set.image f (derivativeOrbit f x)) ∧
          (∀ U : Set (BooleanLift d B),
            connectionSet U →
              derivativeInvariant f U →
                Set.image α.toEquiv U = Set.image f U ∧
                  cayleyAutomorphism U (f.trans α.toEquiv.symm) ∧
                  conjugatesCopies (f.trans α.toEquiv.symm) R T)

end

end MathlibPlus.Open.ResearchFormalization.Claim29206
