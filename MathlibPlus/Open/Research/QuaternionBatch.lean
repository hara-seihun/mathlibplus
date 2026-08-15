import Mathlib

namespace MathlibPlus.Open.Research.QuaternionBatch

abbrev FourFiber (p : ℕ) := ZMod p × Fin 4

def addFour (i j : Fin 4) : Fin 4 :=
  ⟨(i.val + j.val) % 4, Nat.mod_lt _ (by decide)⟩

def chi (p : ℕ) (i : Fin 4) : ZMod p :=
  (-1 : ZMod p) ^ i.val

def generalizedQuaternionChartMul (p : ℕ) (x y : FourFiber p) : FourFiber p :=
  (x.1 + chi p x.2 * y.1, addFour x.2 y.2)

def ChartGroupLaw (p : ℕ) : Prop :=
  (∀ z : FourFiber p,
    generalizedQuaternionChartMul p (0, 0) z = z ∧
      generalizedQuaternionChartMul p z (0, 0) = z) ∧
  (∀ a b c : FourFiber p,
    generalizedQuaternionChartMul p
        (generalizedQuaternionChartMul p a b) c =
      generalizedQuaternionChartMul p a
        (generalizedQuaternionChartMul p b c)) ∧
  (∀ z : FourFiber p, ∃ y : FourFiber p,
    generalizedQuaternionChartMul p z y = (0, 0) ∧
      generalizedQuaternionChartMul p y z = (0, 0))

def generalizedQuaternionPrimeChart : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → 2 < p →
    letI : Fact p.Prime := ⟨hp⟩
    ChartGroupLaw p ∧
    (∀ x y : ZMod p, ∀ i j : Fin 4,
      generalizedQuaternionChartMul p (x, i) (y, j) =
        (x + (-1 : ZMod p) ^ i.val * y, addFour i j)) ∧
    (∀ i : Fin 4, Odd i.val → ∀ y : ZMod p,
      chi p i * y = -y) ∧
    Fintype.card (FourFiber p) = 4 * p

def affineFiberMap (p : ℕ) (L : Fin 4 → (ZMod p)ˣ) (τ : Fin 4 → ZMod p)
    (π : Fin 4 → Fin 4) : FourFiber p → FourFiber p :=
  fun z => (((L z.2 : ZMod p) * z.1 + τ z.2), π z.2)

def scaleFiberMap (p : ℕ) (c : (ZMod p)ˣ) (f : FourFiber p → FourFiber p) :
    FourFiber p → FourFiber p :=
  fun z => (((c : ZMod p) * (f z).1), (f z).2)

def normalizedFiberwiseAffinePresentation (p : ℕ) (f : FourFiber p → FourFiber p) : Prop :=
  ∃ (L : Fin 4 → (ZMod p)ˣ) (τ : Fin 4 → ZMod p) (π : Fin 4 → Fin 4),
    Function.Bijective π ∧ π 0 = 0 ∧ τ 0 = 0 ∧
    (∀ x : ZMod p, ∀ i : Fin 4,
      f (x, i) = ((L i : ZMod p) * x + τ i, π i)) ∧
    ∃ c : (ZMod p)ˣ,
      c * L 0 = 1 ∧
      (∀ x : ZMod p, ∀ i : Fin 4,
        scaleFiberMap p c f (x, i) =
          (((c : ZMod p) * (L i : ZMod p) * x + (c : ZMod p) * τ i), π i))

def relativeDerivativeCoefficient (p : ℕ) (L : Fin 4 → (ZMod p)ˣ)
    (π : Fin 4 → Fin 4) (h k : Fin 4) : ZMod p :=
  (L (addFour h k) : ZMod p) * chi p h -
    chi p (π (addFour h k)) * (chi p (π k))⁻¹ * (L k : ZMod p)

def relativeScalar (p : ℕ) (L : Fin 4 → (ZMod p)ˣ)
    (π : Fin 4 → Fin 4) (k : Fin 4) : ZMod p :=
  (L k : ZMod p) * chi p k * (chi p (π k))⁻¹

def relativeDerivativeCoefficientAndScalarLeftStabilizer : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → 2 < p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (L : Fin 4 → (ZMod p)ˣ) (π : Fin 4 → Fin 4), Function.Bijective π →
      ∀ h : Fin 4,
        (∀ k : Fin 4, relativeDerivativeCoefficient p L π h k = 0) ↔
          (∀ k : Fin 4, relativeScalar p L π (addFour h k) =
            relativeScalar p L π k)

def primeGeneralizedQuaternionAffineShadowTheorem : Prop :=
  ∀ p : ℕ, (hp : Nat.Prime p) → 2 < p →
    letI : Fact p.Prime := ⟨hp⟩
    ChartGroupLaw p ∧
    (∀ x y : ZMod p, ∀ i j : Fin 4,
      generalizedQuaternionChartMul p (x, i) (y, j) =
        (x + (-1 : ZMod p) ^ i.val * y, addFour i j)) ∧
    (∀ i : Fin 4, Odd i.val → ∀ y : ZMod p,
      chi p i * y = -y)

end MathlibPlus.Open.Research.QuaternionBatch
