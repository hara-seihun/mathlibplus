import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim41613

abbrev R1172S3 := FiberMapS3
abbrev R1172Carrier (p : ℕ) := FiberMapCarrier p

def commonFiberEquiv41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    R1172Carrier p ≃ R1172Carrier p :=
  (Equiv.prodCongrLeft q).trans
    (Equiv.prodCongr (Equiv.refl (ZMod p)) sigma)

def rightFiberEquiv41613 (p : ℕ) (x : R1172Carrier p) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.addRight x.1) (Equiv.mulRight x.2)

def inverseFiberEquiv41613 (p : ℕ) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.neg (ZMod p)) (Equiv.inv R1172S3)

def relativeDerivativeEquiv41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (u : ZMod p) (k : R1172S3) :
    R1172Carrier p ≃ R1172Carrier p :=
  let f := commonFiberEquiv41613 p hp sigma hsigma q hq
  let x : R1172Carrier p := (u, k)
  let y := f x
  ((rightFiberEquiv41613 p x).trans f).trans
    ((rightFiberEquiv41613 p (inverseFiberEquiv41613 p y)).trans f.symm)

def normalizedRelativeDerivativeGroup41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    Subgroup (Equiv.Perm (R1172Carrier p)) :=
  Subgroup.closure
    (Set.range (fun x : R1172Carrier p =>
      relativeDerivativeEquiv41613 p hp sigma hsigma q hq x.1 x.2))

def isTranslation41613 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nontranslationSupport41613
    (p : ℕ) (q : R1172S3 → Equiv.Perm (ZMod p)) : Set R1172S3 :=
  {a | a ≠ 1 ∧ ¬ isTranslation41613 p (q a)}

def sectionDerivative41613
    (p : ℕ) (sigma : Equiv.Perm R1172S3)
    (q : R1172S3 → Equiv.Perm (ZMod p))
    (u : ZMod p) (k h : R1172S3) : Equiv.Perm (ZMod p) :=
  ((Equiv.addRight u).trans (q (h * k))).trans
    ((Equiv.addRight (-(q k u))).trans
      (q (thetaK sigma k h)).symm)

def derivativeComparison41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (a h : R1172S3) (u v : ZMod p) : Prop :=
  relativeDerivativeSection31846 p hp sigma hsigma q hq u a ∧
    relativeDerivativeSection31846 p hp sigma hsigma q hq v a ∧
    (sectionDerivative41613 p sigma q v a h).symm.trans
        (sectionDerivative41613 p sigma q u a h) =
      (q (thetaK sigma a h)).symm.trans
        ((Equiv.addRight ((u - q a u) - (v - q a v))).trans
          (q (thetaK sigma a h)))

def primeCycle41613 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ x : ZMod p,
    (∀ y : ZMod p, ∃ j : Fin p, (e ^ (j : ℕ)) x = y) ∧
      (∀ j k : Fin p,
        (e ^ (j : ℕ)) x = (e ^ (k : ℕ)) x → j = k)

def record4Translation41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (a h : R1172S3) : Prop :=
  isTranslation41613 p (q (h * a)) ∧
    ∃ u v : ZMod p,
      (u - q a u) - (v - q a v) ≠ 0 ∧
        derivativeComparison41613 p hp sigma hsigma q hq a h u v ∧
        primeCycle41613 p
          (Equiv.addRight ((u - q a u) - (v - q a v)))

def supportLeftStabilizer41613 (N : Set R1172S3) : Set R1172S3 :=
  {h | ∀ a : R1172S3, a ∈ N ↔ h * a ∈ N}

def derivativeOrbit41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (z : ZMod p) (h : R1172S3) : Set (R1172Carrier p) :=
  {x | ∃ g : normalizedRelativeDerivativeGroup41613 p hp sigma hsigma q hq,
    (g : Equiv.Perm (R1172Carrier p)) (z, h) = x}

def projectedDerivativeComponent41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (z : ZMod p) (h : R1172S3) : Set R1172S3 :=
  {h' | ∃ z' : ZMod p,
    (z', h') ∈ derivativeOrbit41613 p hp sigma hsigma q hq z h}

def fiberSaturated41613
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (z : ZMod p) (h : R1172S3) : Prop :=
  ∀ h' : R1172S3,
    h' ∈ projectedDerivativeComponent41613 p hp sigma hsigma q hq z h →
      ∀ z' : ZMod p,
        (z', h') ∈ derivativeOrbit41613 p hp sigma hsigma q hq z h

def claim41613 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) →
    ∀ (sigma : Equiv.Perm R1172S3), (hsigma : sigma 1 = 1) →
      ∀ (q : R1172S3 → Equiv.Perm (ZMod p)), (hq : q 1 = 1) →
        let N := nontranslationSupport41613 p q
        ∀ h : R1172S3,
          h ∉ supportLeftStabilizer41613 N →
            (∃ a : R1172S3,
              a ∈ N ∧ h * a ∉ N ∧
              record4Translation41613 p hp sigma hsigma q hq a h) ∧
            (∀ z : ZMod p,
              fiberSaturated41613 p hp sigma hsigma q hq z h) ∧
            (∀ (z : ZMod p) (h' : R1172S3),
              ¬ fiberSaturated41613 p hp sigma hsigma q hq z h' →
                h' ∈ supportLeftStabilizer41613 N)

end MathlibPlus.Open.ResearchFormalization.R1172Claim41613
