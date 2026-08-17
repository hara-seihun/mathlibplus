import MathlibPlus.Open.Research.R1661

namespace MathlibPlus.Open.ResearchFormalization.R1661ScalarPowerRepair

/-- A finite-dimensional vector-space carrier over the prime field `ZMod p`. -/
def finiteFpVectorSpace (p : ℕ) (V : Type)
    [AddCommGroup V] [Module (ZMod p) V] : Prop :=
  ∃ r : ℕ, Nonempty (V ≃ₗ[ZMod p] (Fin r → ZMod p))

/-- An affine map whose linear part is `ZMod p`-linear. -/
def fpAffine {p : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (f : Equiv.Perm V) : Prop :=
  ∃ L : V ≃ₗ[ZMod p] V, ∃ b : V, ∀ x : V, f x = b + L x

/--
The radical-algebra presentation of a regular elementary-abelian affine
subgroup.  The multiplication, its algebra laws, the circle operation, and
the evaluation at zero are all tied to the displayed subgroup by the
isomorphism `e`; they are not independent callbacks.
-/
def radicalAlgebraPresentation {p : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (T : Subgroup (Equiv.Perm V)) (mul : V → V → V) : Prop :=
  MathlibPlus.Open.Research.R1661.isRegular T ∧
    MathlibPlus.Open.Research.R1661.isElementaryAbelian p T ∧
    (∀ t : T, fpAffine (p := p) t.1) ∧
    (∀ x : V, mul 0 x = 0) ∧
    (∀ x : V, mul x 0 = 0) ∧
    (∀ x y z : V, mul (x + y) z = mul x z + mul y z) ∧
    (∀ x y z : V, mul x (y + z) = mul x y + mul x z) ∧
    (∀ (a : ZMod p) (x y : V), mul (a • x) y = a • mul x y) ∧
    (∀ (a : ZMod p) (x y : V), mul x (a • y) = a • mul x y) ∧
    (∀ x y : V, mul x y = mul y x) ∧
    (∀ x y z : V, mul (mul x y) z = mul x (mul y z)) ∧
    (∀ x : V, ∃ y : V, x + y + mul x y = 0) ∧
    ∃ e : V ≃ T,
      (∀ x : V, (e x).1 0 = x) ∧
      (∀ x y : V, e (x + y + mul x y) = e x * e y)

/-- The ordinary translation subgroup of an additive permutation carrier. -/
def ordinaryTranslationSubgroup {V : Type} [AddGroup V]
    (T : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ f : Equiv.Perm V, f ∈ T ↔
    ∃ v : V, ∀ x : V, f x = x + v

/--
An affine normalizer inducing a nonidentity scalar power has zero radical
multiplication, and the regular subgroup is the ordinary translation group.
-/
def scalarPowerNormalizerForcesTranslations : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V],
      finiteFpVectorSpace p V →
      ∀ (T : Subgroup (Equiv.Perm V)) (n : Equiv.Perm V)
        (m : ℕ) (mul : V → V → V),
        radicalAlgebraPresentation (p := p) T mul →
        fpAffine (p := p) n →
        MathlibPlus.Open.Research.R1661.normalizesWithPower (V := V) p m T n →
        (m : ZMod p) ≠ 0 → (m : ZMod p) ≠ 1 →
        (∀ x y : V, mul x y = 0) ∧
          ordinaryTranslationSubgroup T

end MathlibPlus.Open.ResearchFormalization.R1661ScalarPowerRepair
