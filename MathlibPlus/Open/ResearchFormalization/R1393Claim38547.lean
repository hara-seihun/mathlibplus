import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1393Claim38547

private def listProduct [Mul α] : List α → Option α
  | [] => none
  | [x] => some x
  | x :: y :: xs =>
      (listProduct (y :: xs)).map (fun z => x * z)

private def idealPowerZero {A : Type*} [Mul A] [Zero A]
    (n : ℕ) : Prop :=
  ∀ xs : List A, xs.length = n → listProduct xs = some 0

private def positivePower [Mul α] [Zero α] : ℕ → α → α
  | 0, _ => 0
  | 1, x => x
  | n + 2, x => positivePower (n + 1) x * x

private def circleMul {A : Type*} [NonUnitalNonAssocRing A]
    (x y : A) : A :=
  x + y + x * y

private def truncatedExponential {p : ℕ} {A : Type*}
    [NonUnitalNonAssocRing A] [Module (ZMod p) A]
    (x : A) : A :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ((Nat.factorial k : ZMod p)⁻¹) • positivePower k x

private def translationSet {A : Type*} [AddGroup A] : Set (Equiv.Perm A) :=
  {g | ∃ a : A, ∀ x : A, g x = x + a}

private def circleTranslationSet {A : Type*}
    [NonUnitalNonAssocRing A] : Set (Equiv.Perm A) :=
  {g | ∃ a : A, ∀ x : A, g x = x + a + x * a}

private def translationGroup {A : Type*} [AddGroup A] :
    Subgroup (Equiv.Perm A) :=
  Subgroup.closure (translationSet (A := A))

private def circleTranslationGroup {A : Type*}
    [NonUnitalNonAssocRing A] : Subgroup (Equiv.Perm A) :=
  Subgroup.closure (circleTranslationSet (A := A))

private def generatedAffineGroup {A : Type*}
    [NonUnitalNonAssocRing A]
    (N T : Subgroup (Equiv.Perm A)) : Subgroup (Equiv.Perm A) :=
  Subgroup.closure ((N : Set (Equiv.Perm A)) ∪ (T : Set (Equiv.Perm A)))

private def gammaSet {A : Type*}
    [NonUnitalNonAssocRing A] : Set (Equiv.Perm A) :=
  {g | ∃ a : A, ∀ x : A, g x = x + x * a}

private def zeroStabilizer {A : Type*}
    [NonUnitalNonAssocRing A]
    (G : Subgroup (Equiv.Perm A)) : Set (Equiv.Perm A) :=
  {g | g ∈ G ∧ g 0 = 0}

private def pointStabilizerOrbit {A : Type*}
    [NonUnitalNonAssocRing A]
    (G : Subgroup (Equiv.Perm A)) (x : A) : Set A :=
  {y | ∃ g : Equiv.Perm A, g ∈ zeroStabilizer G ∧ g x = y}

private def affineIdealCoset {A : Type*}
    [NonUnitalNonAssocRing A] (x : A) : Set A :=
  {y | ∃ a : A, y = x + x * a}

/-- Claim 38547: the truncated exponential fixes every generated suborbit. -/
def truncatedExponentialFixesGeneratedSuborbits : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (A : Type*) [NonUnitalNonAssocRing A]
      [Module (ZMod p) A] [Finite A],
      FiniteDimensional (ZMod p) A →
      Odd p →
      (∀ x y : A, x * y = y * x) →
      (∀ x y z : A, (x * y) * z = x * (y * z)) →
      (∀ (r : ZMod p) (x y : A),
        (r • x) * y = r • (x * y) ∧
          x * (r • y) = r • (x * y)) →
      idealPowerZero (A := A) p →
      let N := translationGroup (A := A)
      let T := circleTranslationGroup (A := A)
      let G := generatedAffineGroup N T
      let q := truncatedExponential (p := p) (A := A)
      zeroStabilizer G = gammaSet (A := A) ∧
        (∀ x : A,
          pointStabilizerOrbit G x = affineIdealCoset x ∧
            (∃ a : A, q x - x = x * a) ∧
            q x ∈ pointStabilizerOrbit G x ∧
            q '' pointStabilizerOrbit G x = pointStabilizerOrbit G x)

end MathlibPlus.Open.ResearchFormalization.R1393Claim38547
