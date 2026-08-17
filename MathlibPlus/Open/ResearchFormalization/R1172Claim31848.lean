import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim31848

abbrev S3 := FiberMapS3
abbrev Carrier (p : ℕ) := FiberMapCarrier p

def commonFiberEquiv31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    Carrier p ≃ Carrier p :=
  (Equiv.prodCongrLeft q).trans
    (Equiv.prodCongr (Equiv.refl (ZMod p)) sigma)

def rightFiberEquiv31848
    (p : ℕ) (x : Carrier p) : Carrier p ≃ Carrier p :=
  Equiv.prodCongr (Equiv.addRight x.1) (Equiv.mulRight x.2)

def inverseFiberEquiv31848 (p : ℕ) : Carrier p ≃ Carrier p :=
  Equiv.prodCongr (Equiv.neg (ZMod p)) (Equiv.inv S3)

def relativeDerivativeEquiv31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (u : ZMod p) (k : S3) :
    Carrier p ≃ Carrier p :=
  let f := commonFiberEquiv31848 p hp sigma hsigma q hq
  let x : Carrier p := (u, k)
  let y := f x
  ((rightFiberEquiv31848 p x).trans f).trans
    ((rightFiberEquiv31848 p (inverseFiberEquiv31848 p y)).trans f.symm)

def relativeDerivativeGroup31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    Subgroup (Equiv.Perm (Carrier p)) :=
  Subgroup.closure
    (Set.range (fun x : Carrier p =>
      relativeDerivativeEquiv31848 p hp sigma hsigma q hq x.1 x.2))

def isTranslation31848 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nontranslationSupport31848
    (p : ℕ) (q : S3 → Equiv.Perm (ZMod p)) : Set S3 :=
  {a | a ≠ 1 ∧ ¬ isTranslation31848 p (q a)}

def sectionDerivative31848
    (p : ℕ) (sigma : Equiv.Perm S3)
    (q : S3 → Equiv.Perm (ZMod p))
    (u : ZMod p) (k h : S3) : Equiv.Perm (ZMod p) :=
  ((Equiv.addRight u).trans (q (h * k))).trans
    ((Equiv.addRight (-(q k u))).trans
      (q (thetaK sigma k h)).symm)

def derivativeComparison31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (a h : S3) (u v : ZMod p) : Prop :=
  (∀ z : ZMod p,
    relativeDerivativeOf31844 p hp sigma hsigma q hq u a (z, h) =
      (sectionDerivative31848 p sigma q u a h z,
        thetaK sigma a h)) ∧
    (∀ z : ZMod p,
      relativeDerivativeOf31844 p hp sigma hsigma q hq v a (z, h) =
        (sectionDerivative31848 p sigma q v a h z,
          thetaK sigma a h)) ∧
    (sectionDerivative31848 p sigma q v a h).symm.trans
        (sectionDerivative31848 p sigma q u a h) =
      (q (thetaK sigma a h)).trans
        ((Equiv.addRight ((u - q a u) - (v - q a v))).trans
          (q (thetaK sigma a h)).symm)

def primeCycle31848 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ x : ZMod p,
    (∀ y : ZMod p, ∃ j : Fin p, (e ^ (j : ℕ)) x = y) ∧
      (∀ j k : Fin p,
        (e ^ (j : ℕ)) x = (e ^ (k : ℕ)) x → j = k)

def record4Translation31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (a h : S3) : Prop :=
  isTranslation31848 p (q (h * a)) ∧
    ∃ u v : ZMod p,
      (u - q a u) - (v - q a v) ≠ 0 ∧
        derivativeComparison31848 p hp sigma hsigma q hq a h u v ∧
        primeCycle31848 p
          (Equiv.addRight ((u - q a u) - (v - q a v)))

def supportLeftStabilizer31848 (N : Set S3) : Set S3 :=
  {h | ∀ a : S3, a ∈ N ↔ h * a ∈ N}

def derivativeOrbit31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (z : ZMod p) (h : S3) : Set (Carrier p) :=
  {x | ∃ g : relativeDerivativeGroup31848 p hp sigma hsigma q hq,
    (g : Equiv.Perm (Carrier p)) (z, h) = x}

def projectedDerivativeComponent31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (z : ZMod p) (h : S3) : Set S3 :=
  {h' | ∃ z' : ZMod p,
    (z', h') ∈ derivativeOrbit31848 p hp sigma hsigma q hq z h}

def fiberSaturated31848
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (z : ZMod p) (h : S3) : Prop :=
  ∀ h' : S3,
    h' ∈ projectedDerivativeComponent31848 p hp sigma hsigma q hq z h →
      ∀ z' : ZMod p,
        (z', h') ∈ derivativeOrbit31848 p hp sigma hsigma q hq z h

def componentsOutsideSupportStabilizerAreSaturated31848 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) →
    ∀ (sigma : Equiv.Perm S3), (hsigma : sigma 1 = 1) →
      ∀ (q : S3 → Equiv.Perm (ZMod p)), (hq : q 1 = 1) →
        let N := nontranslationSupport31848 p q
        ∀ h : S3,
          h ∉ supportLeftStabilizer31848 N →
            (∃ a : S3,
              a ∈ N ∧ h * a ∉ N ∧
              record4Translation31848 p hp sigma hsigma q hq a h) ∧
            (∀ z : ZMod p,
              fiberSaturated31848 p hp sigma hsigma q hq z h) ∧
            (∀ (z : ZMod p) (h' : S3),
              ¬ fiberSaturated31848 p hp sigma hsigma q hq z h' →
                h' ∈ supportLeftStabilizer31848 N)

end MathlibPlus.Open.ResearchFormalization.R1172Claim31848
