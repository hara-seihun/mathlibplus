import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim41612

abbrev R1172S3 := FiberMapS3
abbrev R1172Carrier (p : ℕ) := FiberMapCarrier p

def commonFiberEquiv41612
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    R1172Carrier p ≃ R1172Carrier p :=
  (Equiv.prodCongrLeft q).trans
    (Equiv.prodCongr (Equiv.refl (ZMod p)) sigma)

def rightFiberEquiv41612 (p : ℕ) (x : R1172Carrier p) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.addRight x.1) (Equiv.mulRight x.2)

def inverseFiberEquiv41612 (p : ℕ) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.neg (ZMod p)) (Equiv.inv R1172S3)

def relativeDerivativeEquiv41612
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (u : ZMod p) (k : R1172S3) :
    R1172Carrier p ≃ R1172Carrier p :=
  let f := commonFiberEquiv41612 p hp sigma hsigma q hq
  let x : R1172Carrier p := (u, k)
  let y := f x
  ((rightFiberEquiv41612 p x).trans f).trans
    ((rightFiberEquiv41612 p (inverseFiberEquiv41612 p y)).trans f.symm)

def normalizedRelativeDerivativeGroup41612
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    Subgroup (Equiv.Perm (R1172Carrier p)) :=
  Subgroup.closure
    (Set.range (fun x : R1172Carrier p =>
      relativeDerivativeEquiv41612 p hp sigma hsigma q hq x.1 x.2))

def isTranslation41612 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nontranslationSupport41612
    (p : ℕ) (q : R1172S3 → Equiv.Perm (ZMod p)) : Set R1172S3 :=
  {a | a ≠ 1 ∧ ¬ isTranslation41612 p (q a)}

def sectionDerivative41612
    (p : ℕ) (sigma : Equiv.Perm R1172S3)
    (q : R1172S3 → Equiv.Perm (ZMod p))
    (u : ZMod p) (k h : R1172S3) : Equiv.Perm (ZMod p) :=
  ((Equiv.addRight u).trans (q (h * k))).trans
    ((Equiv.addRight (-(q k u))).trans
      (q (thetaK sigma k h)).symm)

def derivativeComparison41612
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (a h : R1172S3) (u v : ZMod p) : Prop :=
  relativeDerivativeSection31846 p hp sigma hsigma q hq u a ∧
    relativeDerivativeSection31846 p hp sigma hsigma q hq v a ∧
    (sectionDerivative41612 p sigma q v a h).symm.trans
        (sectionDerivative41612 p sigma q u a h) =
      (q (thetaK sigma a h)).symm.trans
        ((Equiv.addRight ((u - q a u) - (v - q a v))).trans
          (q (thetaK sigma a h)))

def primeCycle41612 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ x : ZMod p,
    (∀ y : ZMod p, ∃ j : Fin p, (e ^ (j : ℕ)) x = y) ∧
      (∀ j k : Fin p,
        (e ^ (j : ℕ)) x = (e ^ (k : ℕ)) x → j = k)

def claim41612 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) →
    ∀ (sigma : Equiv.Perm R1172S3), (hsigma : sigma 1 = 1) →
      ∀ (q : R1172S3 → Equiv.Perm (ZMod p)), (hq : q 1 = 1) →
        ∀ (a h : R1172S3),
          a ∈ nontranslationSupport41612 p q →
          h * a ∉ nontranslationSupport41612 p q →
            isTranslation41612 p (q (h * a)) ∧
            (¬ ∃ c : ZMod p, ∀ u : ZMod p, u - q a u = c) ∧
            ∃ u v : ZMod p,
              (u - q a u) - (v - q a v) ≠ 0 ∧
              derivativeComparison41612 p hp sigma hsigma q hq a h u v ∧
              primeCycle41612 p
                (Equiv.addRight ((u - q a u) - (v - q a v)))

end MathlibPlus.Open.ResearchFormalization.R1172Claim41612
