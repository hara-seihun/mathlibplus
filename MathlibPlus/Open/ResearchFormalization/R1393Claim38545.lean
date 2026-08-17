import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1393Claim38545

private def positivePower [Mul α] [Zero α] : ℕ → α → α
  | 0, _ => 0
  | 1, x => x
  | n + 2, x => positivePower (n + 1) x * x

private def idealPowerZero {A : Type*} [Mul A] [Zero A]
    (n : ℕ) : Prop :=
  ∀ xs : List A, xs.length = n →
    (match xs with
    | [] => none
    | x :: ys => some (ys.foldl (fun z y => z * y) x)) = some 0

private def circleMul {A : Type*} [NonUnitalNonAssocRing A]
    (x y : A) : A :=
  x + y + x * y

private def truncatedExponential {p : ℕ} {A : Type*}
    [NonUnitalNonAssocRing A] [Module (ZMod p) A]
    (x : A) : A :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ((Nat.factorial k : ZMod p)⁻¹) • positivePower k x

private def circleGroupLaws {A : Type*} [NonUnitalNonAssocRing A] : Prop :=
  (∀ x y z : A,
    circleMul (circleMul x y) z = circleMul x (circleMul y z)) ∧
    (∀ x : A, circleMul 0 x = x ∧ circleMul x 0 = x) ∧
    (∀ x : A, ∃ y : A,
      circleMul x y = 0 ∧ circleMul y x = 0)

/-- Claim 38545: the truncated exponential is an additive-to-circle isomorphism. -/
def truncatedExponentialIsAdditiveToCircle : Prop :=
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
      circleGroupLaws (A := A) ∧
        Function.Bijective (truncatedExponential (p := p) (A := A)) ∧
        (∀ x y : A,
          truncatedExponential (p := p) (A := A) (x + y) =
            circleMul
              (truncatedExponential (p := p) (A := A) x)
              (truncatedExponential (p := p) (A := A) y))

end MathlibPlus.Open.ResearchFormalization.R1393Claim38545
