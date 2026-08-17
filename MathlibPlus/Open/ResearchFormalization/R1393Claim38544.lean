import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1393Claim38544

private def listProduct [Mul α] : List α → Option α
  | [] => none
  | [x] => some x
  | x :: y :: xs =>
      (listProduct (y :: xs)).map (fun z => x * z)

private def idealPowerZero {A : Type*} [Mul A] [Zero A]
    (n : ℕ) : Prop :=
  ∀ xs : List A, xs.length = n → listProduct xs = some 0

private def nilpotentAlgebra {A : Type*} [Mul A] [Zero A] : Prop :=
  ∃ n : ℕ, 0 < n ∧ idealPowerZero (A := A) n

private def pFoldPower {A : Type*} [Mul A] [Zero A]
    (p : ℕ) (x : A) : Option A :=
  listProduct (List.replicate p x)

/-- Claim 38544: low-dimensional elementwise nilpotence forces ideal-power nilpotence. -/
def lowDimensionElementwiseNilpotenceForcesIdealPowerNilpotence : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (A : Type*) [NonUnitalNonAssocRing A] [Module (ZMod p) A],
      FiniteDimensional (ZMod p) A →
      (∀ x y : A, x * y = y * x) →
      (∀ x y z : A, (x * y) * z = x * (y * z)) →
      (∀ (r : ZMod p) (x y : A),
        (r • x) * y = r • (x * y) ∧
          x * (r • y) = r • (x * y)) →
      nilpotentAlgebra (A := A) →
      Module.finrank (ZMod p) A ≤ 2 * p - 2 →
      (∀ x : A, pFoldPower p x = some 0) →
      idealPowerZero (A := A) p

end MathlibPlus.Open.ResearchFormalization.R1393Claim38544
