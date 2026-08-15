import Mathlib

namespace MathlibPlus.Open

abbrev FiberMapS3 := Equiv.Perm (Fin 3)
abbrev FiberMapCarrier (p : ℕ) := ZMod p × FiberMapS3

def normalizedCommonCoordinateFiberMap31844
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm FiberMapS3)
    (hsigma : sigma 1 = 1)
    (q : FiberMapS3 → Equiv.Perm (ZMod p))
    (hq : q 1 = 1) :
    FiberMapCarrier p → FiberMapCarrier p :=
  fun x => (q x.2 x.1, sigma x.2)

def normalizedCommonCoordinateFiberMap41609
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm FiberMapS3)
    (hsigma : sigma 1 = 1)
    (q : FiberMapS3 → Equiv.Perm (ZMod p))
    (hq : q 1 = 1) :
    FiberMapCarrier p → FiberMapCarrier p :=
  fun x => (q x.2 x.1, sigma x.2)

def fiberMapProductMul (p : ℕ)
    (x y : FiberMapCarrier p) : FiberMapCarrier p :=
  (x.1 + y.1, x.2 * y.2)

def fiberMapProductInv (p : ℕ)
    (x : FiberMapCarrier p) : FiberMapCarrier p :=
  (-x.1, x.2⁻¹)

def fiberMapSection (p : ℕ) (h : FiberMapS3) : Set (FiberMapCarrier p) :=
  {x | x.2 = h}

def fiberMapInverse (p : ℕ)
    (sigma : Equiv.Perm FiberMapS3)
    (q : FiberMapS3 → Equiv.Perm (ZMod p)) :
    FiberMapCarrier p → FiberMapCarrier p :=
  fun x => ((q (sigma.symm x.2)).symm x.1, sigma.symm x.2)

def thetaK (sigma : Equiv.Perm FiberMapS3)
    (k h : FiberMapS3) : FiberMapS3 :=
  sigma.symm (sigma (h * k) * (sigma k)⁻¹)

def relativeDerivativeOf31844
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm FiberMapS3)
    (hsigma : sigma 1 = 1)
    (q : FiberMapS3 → Equiv.Perm (ZMod p))
    (hq : q 1 = 1)
    (u : ZMod p) (k : FiberMapS3) :
    FiberMapCarrier p → FiberMapCarrier p :=
  fun x =>
    fiberMapInverse p sigma q
      (fiberMapProductMul p
        (normalizedCommonCoordinateFiberMap31844 p hp sigma hsigma q hq
          (fiberMapProductMul p x (u, k)))
        (fiberMapProductInv p
          (normalizedCommonCoordinateFiberMap31844 p hp sigma hsigma q hq
            (u, k))))

def relativeDerivativeSection31846
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm FiberMapS3)
    (hsigma : sigma 1 = 1)
    (q : FiberMapS3 → Equiv.Perm (ZMod p))
    (hq : q 1 = 1)
    (u : ZMod p) (k : FiberMapS3) : Prop :=
  (∀ (z : ZMod p) (h : FiberMapS3),
    relativeDerivativeOf31844 p hp sigma hsigma q hq u k (z, h) =
      ( ((q (thetaK sigma k h)).symm)
          (q (h * k) (z + u) - q k u),
        thetaK sigma k h)) ∧
  (∀ (h : FiberMapS3),
    Set.image
      (relativeDerivativeOf31844 p hp sigma hsigma q hq u k)
      (fiberMapSection p h) =
      fiberMapSection p (thetaK sigma k h))

def relativeDerivativeOf41609
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm FiberMapS3)
    (hsigma : sigma 1 = 1)
    (q : FiberMapS3 → Equiv.Perm (ZMod p))
    (hq : q 1 = 1)
    (u : ZMod p) (k : FiberMapS3) :
    FiberMapCarrier p → FiberMapCarrier p :=
  fun x =>
    fiberMapInverse p sigma q
      (fiberMapProductMul p
        (normalizedCommonCoordinateFiberMap41609 p hp sigma hsigma q hq
          (fiberMapProductMul p x (u, k)))
        (fiberMapProductInv p
          (normalizedCommonCoordinateFiberMap41609 p hp sigma hsigma q hq
            (u, k))))

def relativeDerivativeSection41611
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm FiberMapS3)
    (hsigma : sigma 1 = 1)
    (q : FiberMapS3 → Equiv.Perm (ZMod p))
    (hq : q 1 = 1)
    (u : ZMod p) (k : FiberMapS3) : Prop :=
  (∀ (z : ZMod p) (h : FiberMapS3),
    relativeDerivativeOf41609 p hp sigma hsigma q hq u k (z, h) =
      ( ((q (thetaK sigma k h)).symm)
          (q (h * k) (z + u) - q k u),
        thetaK sigma k h)) ∧
  (∀ (h : FiberMapS3),
    Set.image
      (relativeDerivativeOf41609 p hp sigma hsigma q hq u k)
      (fiberMapSection p h) =
      fiberMapSection p (thetaK sigma k h))

end MathlibPlus.Open
